---- MODULE vsr ----
\* 
\* In Progress!
\* 
\* TLA+ Specification for Viewstamped Replication (VSR)
\* Paper: http://pmg.csail.mit.edu/papers/vr-revisited.pdf
\*
\* The structure of this spec is inspired by the RAFT Spec (https://github.com/etcd-io/raft/blob/main/tla/etcdraft.tla)
\* and the VSR Spec (https://github.com/Vanlightly/vsr-tlaplus/blob/main/vsr-revisited/paper/VSR.tla).
\* 
\* Notes:
\*   - View Changes:
\*     The RAFT paper (Section 5.4.1) mentions that in VSR, a leader can be elected even if it does not have the latest state. 
\*     This may cause delays in the cluster becoming active, but this is generally not a practical problem. 
\*     We can increment the view number and initiate a new view change if the current view does not have the latest state or times out. 
\*     (See: https://youtu.be/Wii1LX_ltIs?t=2096)
\*   - Recovery  
\*   - Reconfiguration  
\*   - Client Requests (Not implemented — not required for protocol verification)
\* 
\* Draft Plan:
\*  - Start with f = 1, giving 2f + 1 replicas. Later, aim for f = 2.
\*  - Add optimizations.
\*  - Explore TigerBeetle's implementation.
\*  - Capture TigerBeetle's invariants.
\*
\* TODO:
\* 

EXTENDS Naturals, Integers, Bags, FiniteSets, Sequences, SequencesExt, FiniteSetsExt, BagsExt, TLC

\* Initial set of server IDs {1, 2, 3}; IDs are integer values.
\* TODO: This may need adjustment when reconfiguration is introduced.
CONSTANTS
    \* Viewstamped Replication Servers are logically ordered by their IP addresses (hashed to integers). Here we simply use integers.
    Servers

\* Reserved value
CONSTANTS 
    Nil    

\* Possible server states: Normal, ViewChange, or Recovering.
\* Refer to Figure 2 of the paper for these states.
CONSTANTS 
    \* Primary & Replica roles can be derived from the view number, 
    \* but we explicitly define these to ensure the primary/replica designation aligns with the view number for invariants checking.
    PrimaryNormal,
    ReplicaNormal,
    \* Initial state
    ViewChange,
    Recovering

\* Message Types
\* Search for the symbol 〈 in the paper to locate message types.
\* TODO: Currently not all message types are used; recovery and reconfiguration messages are ignored for now.
\* XXX Client Messages: Not used in this specification.
CONSTANTS
    \* Request from Client to Primary: 〈REQUEST op, c, s〉 
    \*  op: Operation
    \*  c: Client ID
    \*  s: Request number assigned by the client
    RequestMsg,
    \* Sent by Primary to Replica after appending a request to its log: 〈PREPARE v, m, n, k〉
    \*  v: View number
    \*  m: Client message
    \*  n: Operation number (index in log)
    \*  k: Commit number (index of last committed log entry)
    PrepareMsg,
    \* Sent by Replica to Primary after successfully appending a message: 〈PREPAREOK v, n, i〉
    \*  v: View number
    \*  n: Operation number (index in log)
    \*  i: Replica ID
    PrepareOkMsg,
    \* After receiving PrepareOk from the majority of replicas, Primary updates the state machine and increments the commit number.
    \*  Then sends 〈REPLY v, s, x〉 to the client.
    \*  v: View number
    \*  s: Request number from client
    \*  x: Result of the up-call
    ReplyMsg,
    \* If client requests exist, Primary periodically sends 〈COMMIT v, k〉 (as a heartbeat) to all Replicas.
    \*  v: View number
    \*  k: Commit number; in this case, commit number equals operation number as there are client requests.
    CommitMsg,
    \* Normally, Primary sends Prepare or Commit messages. If a Replica times out without messages from Primary,
    \*  or receives StartViewChangeMsg with a higher view number from another Replica, it increments its view number
    \*  and sends 〈STARTVIEWCHANGE v, i〉 to all other replicas.
    \*  v: New View number
    \*  i: Replica ID
    StartViewChangeMsg,
    \* After receiving StartViewChangeMsg from a majority, a Replica sends 〈DOVIEWCHANGE v, l, v’, n, k, i〉 to the new primary.
    \*  v: View number
    \*  l: Replica's log
    \*  v’: Latest normal view for this replica
    \*  n: Operation number (index in log)
    \*  k: Commit number
    \*  i: Replica ID
    DoViewChangeMsg,
    \* After receiving DoViewChangeMsg from the majority:
    \*  - Sets view number from message.
    \*  - Chooses the log from the message with the highest view number; if tied, the highest op number.
    \*  - Updates op/commit number and changes state to Normal.
    \*  - Broadcasts 〈STARTVIEW v, l, n, k〉 to all Replicas.
    \*  v: View number
    \*  l: Log
    \*  n: Operation number
    \*  k: Commit number
    StartViewMsg,
    \*  TODO: To be implemented later
    RecoveryMsg,
    RecoveryResponseMsg,
    GetStateMsg,
    NewStateMsg,
    \* TODO: To be implemented later
    ReconfigurationMsg,
    StartEpochMsg,
    EpochStartedMsg,
    CheckEpochMsg,
    NewEpochMsg

VARIABLES
    \* Server state: Int -> State (e.g., 1 -> PrimaryNormal)
    state,
    \* Server View number: Int -> Int (e.g., 1 -> 0)
    viewNumber

serverVars == <<state, viewNumber>>

VARIABLES 
    \* Server log: Int -> Sequence
    log,
    \* Server Op number: Int -> Int (length of the log if never truncated)
    opNumber,
    \* Server Commit number: Int -> Int (last committed operation number)
    commitNumber

logVars == <<log, opNumber, commitNumber>>

VARIABLES
    \* Bag (TLA+ Bag) of messages in the network — independent of servers.
    \* Models unreliable network with duplication, reordering, and message loss.
    networkMessages,
    \* Staging area for messages not yet sent to the network; per-server.
    \* Messages are consumed directly from networkMessages — not from pendingMessages.
    \* Unlike RAFT (which uses a global bag), we maintain pendingMessages as a per-server map for simplicity.
    \* See: https://github.com/etcd-io/raft/blob/main/tla/etcdraft.tla#L176C1-L176C19
    \* Int -> Bag of messages
    pendingMessages

messageVars == <<networkMessages, pendingMessages>>

VARIABLES
    \* Server i has to receive StartViewChange from atleast f servers, including i itself, to initiate a view change.
    \* So in total, f + 1 servers must send StartViewChange. (Including itself)
    \* Int -> Int 
    receivedSvcCnt,
    \* Int -> DoViewChangeMsg
    \* As per the paper 4.2 & 3rd bullet point, 
    \*   selects as the new log the one contained in the message with the largest v′ (last normal view number); 
    \*   if several messages have the same v′ it selects the one among them with the largest n (operation number).
    \* As these decisions are made based on the DoViewChange messages received, we store the messages here.
    receivedDvcMessages,
    \* Int -> Int
    lastNormalViewNumber

viewChangeVars == <<receivedSvcCnt, receivedDvcMessages, lastNormalViewNumber>>

\* Used for stuttering
vars == <<serverVars, logVars, messageVars, viewChangeVars>>

\* Helpers

\* Returns the bag 'msgs' with message 'm' added.
\* Used to add a message to networkMessages or pendingMessages.
WithMessage(m, msgs) == msgs (+) SetToBag({m})

\* Returns the bag 'msgs' with message 'm' removed.
\* Used to remove/discard a message from networkMessages or pendingMessages.
WithoutMessage(m, msgs) == msgs (-) SetToBag({m})

\* Discards message 'm' from networkMessages — modeling unreliable delivery.
\* Or removes a message after processing it.
Discard(m) ==
    networkMessages' = WithoutMessage(m, networkMessages)

\* Empties the pending messages bag for server i — models message loss due to crash or restart.
ClearPendingMessages(i) ==
    pendingMessages' = [pendingMessages EXCEPT ![i] = EmptyBag]

\* Sends all of server i's pending messages to networkMessages.
SendPendingMessagesToNetworkMessages(i) ==
    /\ networkMessages' = networkMessages (+) pendingMessages[i]
    /\ pendingMessages' = [pendingMessages EXCEPT ![i] = EmptyBag]       

\* Total number of servers (replicas).
ServerCount == Cardinality(Servers)

\* Computes the Primary server ID based on the view number.
\* View number is 0-based.
\* Example:
\* View number = 0, Server count = 3 => Primary = 1
\* View number = 1, Server count = 3 => Primary = 2
\* View number = 2, Server count = 3 => Primary = 3
\* View number = 3, Server count = 3 => Primary = 1
GetPrimaryFromViewNumber(v) == 
    (v % ServerCount) + 1

\* Returns TRUE if server i is Primary in its current view.
IsPrimaryFromViewNumber(i) == 
    GetPrimaryFromViewNumber(viewNumber[i]) = i

\* Checks if server i is in PrimaryNormal state.
IsPrimary(i) == 
    state[i] = PrimaryNormal

\* Define the initial system state.
InitMessageVars ==
    /\ networkMessages = EmptyBag
    /\ pendingMessages = [i \in Servers |-> EmptyBag]

\* Though Primary is known to be server 1 at init, we do not assume this; 
\* all servers start in ViewChange state and elect the Primary.
\* The view number will increment due to view change upon cluster start.
InitServerVars ==
    /\ state = [i \in Servers |-> ViewChange]
    /\ viewNumber = [i \in Servers |-> 0]

InitLogVars ==
    /\ log = [i \in Servers |-> <<>>]
    /\ opNumber = [i \in Servers |-> 0]
    /\ commitNumber = [i \in Servers |-> 0]    

InitViewChangeVars ==
    /\ receivedSvcCnt = [i \in Servers |-> 0]
    /\ receivedDvcMessages = [i \in Servers |-> {}]
    \* As per this implementation, as we start with view 0 in ViewChange state, there is no last normal view number.
    \* This is set to -1, indicating no normal view has been established yet.
    /\ lastNormalViewNumber = [i \in Servers |-> -1]    

Init ==
    /\ InitMessageVars
    /\ InitServerVars
    /\ InitLogVars
    /\ InitViewChangeVars

\* Message creation

ResetViewChangeVars(i) ==
    /\ receivedSvcCnt' = [receivedSvcCnt EXCEPT ![i] = 0]
    /\ receivedDvcMessages' = [receivedDvcMessages EXCEPT ![i] = {}]

StartViewChangeMessage(iSource, advViewNumber) ==
    [type           |-> StartViewChangeMsg,
     advViewNumber  |-> advViewNumber,
     source         |-> iSource,
     target         |-> Nil] \* Replaced with iTarget during broadcast, since message is sent to all replicas.

DoViewChangeMessage(iSource) ==
    [type               |-> DoViewChangeMsg,
     viewNumber         |-> viewNumber[iSource],
     log                |-> log[iSource],
     lastNormalView     |-> lastNormalViewNumber[iSource],
     opNumber           |-> opNumber[iSource],
     commitNumber       |-> commitNumber[iSource],
     source             |-> iSource,
     \*  Only the new primary will receive this message.
     target             |-> GetPrimaryFromViewNumber(viewNumber[iSource])]

StartViewMessage(viewNumber, log, opNumber, commitNumber, iSource) ==
    [type           |-> StartViewMsg,
     viewNumber     |-> viewNumber,
     log            |-> log,
     opNumber       |-> opNumber,
     commitNumber   |-> commitNumber,
     source         |-> iSource,
     target         |-> Nil] \* Replaced with iTarget during broadcast, since message is sent to all replicas.

PrepareOkMessage(iSource, opNumber, iTarget) ==
    [type           |-> PrepareOkMsg,
     viewNumber     |-> viewNumber[iSource],
     opNumber       |-> n,
     source         |-> iSource,
     target         |-> iTarget]     

\* Broadcast message 'm' to all servers except iSource.
BroadCastMessage(m, iSource) ==
    pendingMessages' = [i \in Servers |-> 
        IF i = iSource 
        THEN pendingMessages[i] 
        ELSE WithMessage(m, pendingMessages[i])]

\* State transition actions

\* Replica i times out and initiates a view change. 
\* Note: TLA+ has no real-time notion of timeout; this is simply another action.
\* See Section 4.2 of the paper.
OnTimeOutStartViewChange(i) ==
    \* Primary will never trigger StartViewChange. Replicas do this after missed heartbeats (Commits) or PrepareOk messages.
    /\ ~IsPrimary(i)
    /\ viewNumber' = [viewNumber EXCEPT ![i] = viewNumber[i] + 1]
    /\ state' = [state EXCEPT ![i] = ViewChange]
    \* Note: View number updates and pendingMessage updates both happen in the next step.
    /\ BroadCastMessage(StartViewChangeMessage(i, viewNumber[i] + 1), i)
    \* As we are starting a new view, we set receivedSvcCnt to 1, indicating this is the first request for a new view change.
    \* When counting receivedSvcCnt, we include the current server i for total required replicas f.
    /\ receivedSvcCnt' = [receivedSvcCnt EXCEPT ![i] = 1]
    /\ receivedDvcMessages' = [receivedDvcMessages EXCEPT ![i] = {}]
    \* Incoming old-view messages for server i in networkMessages will be ignored in the new view; no discard needed.
    \* No need to clear pendingMessages — server is not restarting, only changing view.
    /\ UNCHANGED <<logVars, networkMessages, lastNormalViewNumber>>

\* Check if given message m matches messageType & iTarget, Returns TRUE if it does.
ReceiveMessage(iTarget, messageType, m) ==
    /\ m.type             = messageType
    /\ m.target           = iTarget
    /\ networkMessages[m] > 0

\* Integer division of 2f + 1 results in f, for Quorum we need f + 1.
\* If f are accepted failures, we need f + 1 to ensure a majority.
QuorumSize == (ServerCount \div 2) + 1      

\* If you consider, self Server is also part of the quorum, then remaining servers needed for quorum is QuorumSize - 1.
QuorumIncludingSelf == QuorumSize - 1

\* Replica i receives a StartViewChange message from another replica.
\* If the view number is higher than its own, it initiates a view change by advancing its view number and broadcasting
\* simillar to OnTimeOutStartViewChange.
OnStartViewChangeMessage(i) == 
    \E m \in networkMessages:
        /\ ReceiveMessage(i, StartViewChangeMsg, m)
        \* This replica is seeing a view change message from another replica first time for the new view.
        /\ m.advViewNumber > viewNumber[i]
        /\ viewNumber'     = [viewNumber EXCEPT ![i] = m.advViewNumber]
        /\ state'          = [state EXCEPT ![i] = ViewChange]
        \* Broadcast StartViewChange to all other replicas.
        /\ BroadCastMessage(StartViewChangeMessage(i, m.advViewNumber), i)
        \* As this is the first request for new view change, instead of incrementing we are setting receivedSvcCnt to 1.
        /\ receivedSvcCnt' = [receivedSvcCnt EXCEPT ![i] = 1]
        \* It also never seen a DoViewChange message for this view, so reset it.
        /\ receivedDvcMessages' = [receivedDvcMessages EXCEPT ![i] = {}]
        /\ Discard(m)
        /\ UNCHANGED <<logVars, networkMessages, lastNormalViewNumber>>

OnDoViewChangeMessage(i) ==
    \E m \in networkMessages:
        /\ ReceiveMessage(i, DoViewChangeMsg, m)
        \* Only primary for the new view can receive DoViewChange messages.
        /\ GetPrimaryFromViewNumber(m.advViewNumber) = i
        \* This replica is seeing a DoViewChange message for the first time for the new view.
        /\ m.advViewNumber > viewNumber[i]
        /\ viewNumber'     = [viewNumber EXCEPT ![i] = m.advViewNumber]
        /\ state'          = [state EXCEPT ![i] = ViewChange]
        \* Broadcast StartViewChange to all other replicas.
        /\ BroadCastMessage(StartViewChangeMessage(i, m.advViewNumber), i)
        \* Instead of Union, we are setting receivedDvcCnt to {m}. As this is the first request for new view change.
        /\ receivedDvcMessages' = [receivedDvcMessages EXCEPT ![i] = {m}]
        \* It also never seen a StartViewChange message for this view, so reset it.
        /\ receivedSvcCnt' = [receivedSvcCnt EXCEPT ![i] = 0]
        /\ Discard(m)
        \* No change to logVars.
        /\ UNCHANGED <<logVars, networkMessages, lastNormalViewNumber>>

OnMatchingStartViewChangeMessage(i) ==
    \E m \in networkMessages:
        /\ ReceiveMessage(i, StartViewChangeMsg, m)
        \* This replica has already seen a StartViewChange message for this view.
        \* No need to broadcast StartViewChange as we would have done already.
        /\ m.advViewNumber = viewNumber[i]
        /\ receivedSvcCnt' = [receivedSvcCnt EXCEPT ![i] = receivedSvcCnt[i] + 1]
        /\ Discard(m)
        /\ UNCHANGED <<logVars, state, receivedDvcMessages, lastNormalViewNumber, networkMessages>>        

OnMatchingDoViewChangeMessage(i) ==
    \E m \in networkMessages:
        /\ ReceiveMessage(i, DoViewChangeMsg, m)
        \* Only primary for the new view can receive DoViewChange messages.
        /\ GetPrimaryFromViewNumber(m.advViewNumber) = i
        \* This replica has already seen a DoViewChange message for this view.
        \* No need to broadcast StartViewChange as we would have done already.
        /\ m.advViewNumber = viewNumber[i]
        /\ receivedDvcMessages' = [receivedDvcMessages EXCEPT ![i] = receivedDvcMessages[i] \union {m}]
        /\ Discard(m)
        /\ UNCHANGED <<logVars, state, receivedSvcCnt, lastNormalViewNumber, networkMessages>>        

\* Section 4.2 & 2 bullet point of the VSR paper.
PublishDoViewChangeMessage(i) ==
    /\ status[i] = ViewChange
    \* Received more than f+1 StartViewChange messages, so we can proceed with DoViewChange.
    /\ receivedSvcCnt[i] >= QuorumSize
    /\ LET m = DoViewChangeMessage(i)
       IN 
            \*  This replica is primary for the new view, no need to send DoViewChange to itself. 
         \/ /\ IsPrimaryFromViewNumber(i)
            /\ receivedDvcMessages' = [receivedDvcMessages EXCEPT ![i] = receivedDvcMessages[i] \union {m}]
            /\ UNCHANGED <<pendingMessages>>
         \/ /\ ~IsPrimaryFromViewNumber(i)
            /\ pendingMessages' = [pendingMessages EXCEPT ![i] = WithMessage(m, pendingMessages[i])]
            /\ UNCHANGED <<receivedDvcMessages>>
    /\ UNCHANGED <<logVars, networkMessages, serverVars, receivedSvcCnt, lastNormalViewNumber>>

\* When called, there are DoViewChange messages from a majority of replicas. Thus CHOOSE will not fail.
\* Means receivedDvcMessages[i] will always have equal or more than Quorum messages.
HighestLogMessage(i) ==
    LET m == CHOOSE m \in receivedDvcMessages[i]:
                ~\E m1 \in receivedDvcMessages[i]:
                    \/ m1.lastNormalView > m.lastNormalView
                    \/ /\ m1.lastNormalView = m.lastNormalView 
                       /\ m1.opNumber > m.opNumber
    IN m

HighestCommitNumber(i) ==
    LET m == CHOOSE m \in receivedDvcMessages[i]:
                ~\E m1 \in receivedDvcMessages[i]:
                    m1.commitNumber > m.commitNumber
    IN m.commitNumber    

PublishStartViewMessage(i) ==
    \* Though the paper mentions to set the view number, i think it is already set in previous steps
    /\ status[i] = ViewChange
    /\ Cardinality(receivedDvcMessages[i]) >= QuorumSize
    /\ IsPrimaryFromViewNumber(i)
    /\ LET m                    == HighestLogMessage(i)
           highestCommitNumber  == HighestCommitNumber(i)
       IN
           /\ state'                = [state EXCEPT ![i] = PrimaryNormal]
           /\ log'                  = [log EXCEPT ![i] = m.log]
           /\ opNumber'             = [opNumber EXCEPT ![i] = m.opNumber]
           /\ commitNumber'         = [commitNumber EXCEPT ![i] = highestCommitNumber]
           /\ lastNormalViewNumber' = [lastNormalViewNumber EXCEPT ![i] = viewNumber[i]]
           /\ BroadCastMessage(StartViewMessage(viewNumber[i], m.log, m.opNumber, highestCommitNumber, i), i)
           \* As leader is elected we can clear the view change variables.   
           /\ ResetViewChangeVars(i)     
    /\ UNCHANGED <<networkMessages, viewNumber>>

OnStartViewMessage(i) ==
    \E m \in networkMessages:
        /\ ReceiveMessage(i, StartViewMsg, m)
        \* This node is a backup (replica) for the new view.
        /\ GetPrimaryFromViewNumber(m.viewNumber) # i
        \* Update log, opNumber, commitNumber, and state from the message.
        /\ log'          = [log EXCEPT ![i] = m.log]
        /\ opNumber'     = [opNumber EXCEPT ![i] = m.opNumber]
        /\ commitNumber' = [commitNumber EXCEPT ![i] = m.commitNumber]
        /\ state'        = [state EXCEPT ![i] = ReplicaNormal]
        /\ lastNormalViewNumber' = [lastNormalViewNumber EXCEPT ![i] = viewNumber[i]]
        \* Update view number to the new view number. If it had participated in a view change, 
        \* it would have already been updated.
        /\ viewNumber'   = [viewNumber EXCEPT ![i] = m.viewNumber]
        \* As leader is elected we can clear the view change variables.   
        /\ ResetViewChangeVars(i)
        /\ IF commitNumber[i] < m.opNumber
           THEN 
                LET pkm = PrepareOkMessage(i, m.opNumber, GetPrimaryFromViewNumber(m.viewNumber))
                IN
                /\ pendingMessages' = [pendingMessages EXCEPT ![i] = WithMessage(pkm, pendingMessages[i])]
                /\ Discard(m)
           ELSE /\ Discard(m)
                /\ UNCHANGED <<pendingMessages>>
        \* No change to networkMessages or pendingMessages.
        /\ UNCHANGED <<>>
               




Next ==
    \E i \in Servers: 
       \/ OnTimeOutStartViewChange(i)
       \/ OnViewChangeMessage(i)

====