---- MODULE vsr ----
\*
\* TLA+ Specification for Viewstamped Replication (VSR)
\* Paper: http://pmg.csail.mit.edu/papers/vr-revisited.pdf
\*
\* Structure of Spec is inspired from RAFT Spec https://github.com/etcd-io/raft/blob/main/tla/etcdraft.tla
\* and VSR Spec https://github.com/Vanlightly/vsr-tlaplus/blob/main/vsr-revisited/paper/VSR.tla
\* 
\* Notes:
\*   - View Changes
\*     RAFT Paper mentions (5.4.1) that in VSR leader can be elected even if the leader does not have the latest state. Which might cause delay in 
\*     cluster to become active, but I think it is not a problem in practice. As we can increment view number and start a new view change if 
\*     if current view does not have the latest state or times out. Same is mentioned here https://youtu.be/Wii1LX_ltIs?t=2096
\*   - Recovery  
\*   - Reconfiguration  
\*   - Client Requests (Not implemented, Not required for Protocol Verification)
\* 
\* Draft:
\*  - Will start with f = 1. so we will have 2f + 1 replicas. Finally we will try for f = 2.
\*  - Optimizations
\*  - Tigerbeetles implementation
\* - Tigerbeetles invariants 
\*
\* TODO:
\* 

EXTENDS Naturals, Integers, Bags, FiniteSets, Sequences, SequencesExt, FiniteSetsExt, BagsExt, TLC

\* Inital set of server Ids {1, 2, 3}, Ids are integer values.
\* TODO: When reconfiguration is introduced we might have to change this.
CONSTANTS
    \* Viewstamped Replication Servers are ordered by their IP addresses (hashing to int), In place of IP addresses we are using integers 
    Servers

\* Reserved value
CONSTANTS 
    Nil    

\* Status of the servers, Can be Normal, ViewChange or Recovering.
\* Refer to paper Figure 2 for states defined
CONSTANTS 
    \* Primmary & Replica are not required as it can be calculated from the view number
    \* As we do not want to assume primary based on view number, we will keep these states, to check the invariant if View and Primary/Replica are in sync
    PrimaryNormal,
    ReplicaNormal,
    \* This state is our initial state
    ViewChange,
    Recovering

\* Message Types
\* Search for〈 in paper for message types
\* TODO We are not using all message types, ignoring recovery and reconfiguration messages for now
\* XXX Client Messages: Not used in this spec
CONSTANTS
    \* Request sent by a Client to Primary, 〈REQUEST op, c, s〉 
    \*  op: Operation
    \*   c: Client Id
    \*   s: request number assigned to the request
    RequestMsg,
    \* Sent by Primary to Replica after appending request to its log 〈PREPARE v, m, n, k〉
    \*  v: View number
    \*  m: Message from client
    \*  n: Op number, it is index in the log
    \*  k: Commit number, it is the index of the last committed entry in the log (Where state machine is at)
    PrepareMsg,
    \* Sent by Replica to Primary after succesfully appending received message to its log, 〈PREPAREOK v, n, i〉
    \*  v: View number
    \*  n: Op number, it is index in the log
    \*  i: Id of the Replica
    PrepareOkMsg,
    \* Primary after waiting for PrepareOk from majority of Replica, updates state machine (up-call) and increments commit number
    \*  Then sends 〈REPLY v, s, x〉to the client
    \*  v: View number
    \*  s: Request number assigned by client
    \*  x: Result of the up-call
    ReplyMsg,
    \* If there are client requests, Primary sends 〈COMMIT v, k〉like a heartbeat, periodically to all Replicas
    \*  v: View number
    \*  k: Commit number, in this case commit number is same as operation number, as there are client requests
    CommitMsg,
    \* Normally primary either sends Prepare or Commit messages, if a timeout expires wihtout communication from the primary,
    \*  or if replica receieves StartViewChangeMsg from another replica, with a view number greater than its own then
    \* Replica i advances view number and sends a 〈STARTVIEWCHANGE v, i〉to all other replicas
    \* v: Advanced View number 
    \* i: Id of the Replica
    StartViewChangeMsg,
    \* When a replica receives StartViewChangeMsg from majority of replicas for its advanced view number, 
    \* it sends 〈DOVIEWCHANGE v, l, v’, n, k, i〉to the node that will be the primary in the new view
    \*  v: View number
    \*  l: Replica Log entries
    \*  v’: Latest View number of the replica in which its status is Normal
    \*  n: Op number, it is index in the log
    \*  k: Commit number, it is the index of the last committed entry
    \*  i: Id of the Replica
    DoViewChangeMsg,
    \* After receiving DoViewChangeMsg from majority of replicas, it sets its view number to that in the messages
    \* Selects a new log the once contained in the message with the highest view number, if several messages have the same view number,
    \* it selects the one with the largest operation number
    \* Updates with latest op number and commit number with largest received and changes status to Normal
    \* Then informs all replicas about the new view by sending 〈STARTVIEW v, l, n, k〉
    \*  v: View number
    \*  l: Log entries
    \*  n: Op number, it is index in the log
    \*  k: Commit number, it is the index of the last committed entry
    StartViewMsg,
    \*  TODO Later
    RecoveryMsg,
    RecoveryResponseMsg,
    GetStateMsg,
    NewStateMsg,
    \* TODO Later
    ReconfigurationMsg,
    StartEpochMsg,
    EpochStartedMsg,
    CheckEpochMsg,
    NewEpochMsg


VARIABLES
    \* Server state Int -> State, Example 1 -> PrimaryNormal, 2 -> ReplicaNormal, 3 -> ViewChange, 4 -> Recovering
    state,
    \* Server View number Int -> Int, Example 1 -> 0, 2 -> 1, 3 -> 2
    viewNumber

serverVars == <<state, viewNumber>>

VARIABLES 
    \* Server Log Int -> Seq
    log,
    \* Server Int -> Int, Basically length of the log if log was never truncated
    opNumber,
    \* Server Int -> Int, Last committed operation number, index till which state machine is updated
    commitNumber

logVars == <<log, opNumber, commitNumber>>

VARIABLES
    \* Bag (TLA+ Bag) of messages sent by servers to network, Independent of the servers.
    \* Helps to model the unreliable network with duplicates, reordering and loss of messages
    \* We would have different operators to read messages into server, like
    \* /\ operator1
    \* /\ operator2
    \* /\ operator3. etc.
    \* Thus messages are read from the networkMessages are read in out of order due to "or" between operators
    \* Unreliable network is modeled by discarding messages and
    \* Duplicates are modeled by adding duplicate messages to the networkMessages
    networkMessages,
    \* Staging area for messages that are not yet sent to network, but will be sent in the next step
    \* Each server has its own staging area for pending messages
    \* Not used for receiving messages, messages are read directly from the networkMessages and actions are performed
    \* In RAFT implementation, pendingMessages are agnostic to the server, so it is a single bag and it retrieves messages of server using operator PendingMessages(i) 
    \* on demand, but here we are using pendingMessages as a map from server id to bag of messages to keep it simple
    \* https://github.com/etcd-io/raft/blob/main/tla/etcdraft.tla#L176C1-L176C19
    \* Int -> Bag of messages
    pendingMessages

messageVars == <<networkMessages, pendingMessages>>

\* Used for stuttering
vars == <<serverVars, logVars, messageVars>>

\* Helpers

\* Retrurns the bag of messages by adding the message m to the bag msgs
\* Helps us to add messge to networkMessages or pendingMessages
WithMessage(m, msgs) == msgs (+) SetToBag({m})

\* Returns the bag of messages by removing the message m from the bag msgs
\* Helps us to remove message from networkMessages or pendingMessages or discard message (unreliable network)
WithoutMessage(m, msgs) == msgs (-) SetToBag({m})

\* Discard message from networkMessages, to model unreliable network
\* Also helps to remove message from networkMessages after it has been processed
Discard(m) ==
    networkMessages' = WithoutMessage(m, networkMessages)

\* Returns the empty bag of messages for server i
\* Helps us to model loss of messages due to server i crash or restart
ClearPendingMessages(i) ==
    pendingMessages' = [pendingMessages EXCEPT ![i] = EmptyBag]

\* Adds message m to the pending messages of server i
SendToPendingMessages(m, i) == 
    pendingMessages' = [pendingMessages EXCEPT ![i] = WithMessage(m, pendingMessages[i])]

\* Send all pending messages of server i to the networkMessages
SendPendingMessagesToNetworkMessages(i) ==
    /\ networkMessages' = networkMessages (+) pendingMessages[i]
    /\ pendingMessages' = [pendingMessages EXCEPT ![i] = EmptyBag]       

\* Server count or replica count
ServerCount == Cardinality(Servers)

\* Computes the primary server id based on the view number
\* View number is 0 based
\* View number = 0; Server count = 3; Replica id = 1
\* View number = 1; Server count = 3; Replica id = 2
\* View number = 2; Server count = 3; Replica id = 3
\* View number = 3; Server count = 3; Replica id = 1
GetPrimaryFromViewNumber(v) == 
    (v % ServerCount) + 1

\* Computes the state of server i based on its view number
IsPrimaryFromViewNumber(i) == 
    GetPrimaryFromViewNumber(viewNumber[i]) = i

\* Checks if state of server i is PrimaryNormal
IsPrimary(i) == 
    state[i] = PrimaryNormal    

\* Debugging helpers
PrintState ==
    /\ UNCHANGED <<vars>>
    /\ PrintT("Message Vars: ")
    /\ PrintT(messageVars)
    /\ PrintT("Server Vars: ")
    /\ PrintT(serverVars)
    /\ PrintT("Log Vars: ")
    /\ PrintT(logVars)
    /\ PrintT("In intial state Primary is 1: ")
    /\ PrintT(IsPrimaryFromViewNumber(1))
    

\* Define initial state of the system
InitMessageVars ==
    /\ networkMessages = EmptyBag
    /\ pendingMessages = [i \in Servers |-> EmptyBag]

\* Though we know the primary at init, which is 1, we do not assume it in the spec, we start in ViewChange state and expect the primary to be elected
\* This would make view number to 1 due to view change, when cluster is started.
InitServerVars ==
    /\ state = [i \in Servers |-> ViewChange]
    /\ viewNumber = [i \in Servers |-> 0]

InitLogVars ==
    /\ log = [i \in Servers |-> <<>>]
    /\ opNumber = [i \in Servers |-> 0]
    /\ commitNumber = [i \in Servers |-> 0]    

Init ==
    /\ InitMessageVars
    /\ InitServerVars
    /\ InitLogVars

\* Messages

StartViewChangeMessage(iSource, advViewNumber) ==
    [type           |-> StartViewChangeMsg,
     advViewNumber  |-> advViewNumber,
     source         |-> iSource,
     dest           |-> Nil] \* Replaced with iTarget, in broadcast, as it is sent to all replicas

\* Broadcast to all other servers, except the source server
BroadCastMessage(m, iSource) ==
    {SendToPendingMessages(m, iTarget) : iTarget \in Servers \ {iSource}}

\* Actions performed for state transitions

\* Replica i times out and starts view change, Note that there is no actual timeout in TLA+, This is just another action that can be triggered
\* which is triggered at equal precedence as other actions.
\* Section 4.2 of the paper
TimeOutStartViewChange(i) ==
    \* Primary will never trigger StartViewChange, Replicas in response to missing heartbeat or PrepareOk messages
    /\ ~IsPrimary(i)
    /\ viewNumber' = [viewNumber EXCEPT ![i] = viewNumber[i] + 1]
    /\ state' = [state EXCEPT ![i] = ViewChange]
    \* It would look like viewNumber is updated in next step and message is sent in current step, but it is not the case,
    \* even messages are sent in the next step, as pendingMessages are updated in the next step in SendToPendingMessages
    /\ BroadCastMessage(StartViewChangeMessage(i, viewNumber[i] + 1), i)
    \* At this point, there will be messages to server i in networkMessages, which will be read in the next step, as they would belong older view are ignored
    \* as they are not relevant for the new view, so there is no need to discard them
    \* Similarly, we do not need to clear pending messages, as it would be wrong to do so, as we are not restarting the server, we are just changing the view
    /\ UNCHANGED <<logVars, networkMessages>>

Next ==
    PrintState            
====