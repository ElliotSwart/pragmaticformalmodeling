---------------------------- MODULE naive ----------------------------
EXTENDS Naturals, Sequences

(***************************************************************************)
(* Our "Test Data". Each of these is a set of ids, relevant only in that   *)
(* they are distinct from each other.                                      *)
(***************************************************************************)

CONSTANTS 
    USERIDS, \* A set of userIds to test with (one per user)
    SERVERS, \* A set of serverIds (each one will "create" a new server)
    METADATAS, \* A set of metadata versions. 
    IMAGES \* A set of image versions.

(***************************************************************************)
(* Our variables update each step and represent the state of our modeled   *)
(* system.                                                                 *)
(***************************************************************************)
VARIABLES
    (***********************************************************************)
    (* These variables are relevant to the implementation.                 *)
    (***********************************************************************)
    databaseState, \* databaseState[key] = What is stored for this key
    blobStoreState, \* blobStoreState[key] = What is stored for this key
    serverStates, \* serverStates[serverId] = What the server is doing
    
    (***********************************************************************)
    (* This variable is used to observe the state of the system to         *)
    (* check if it's doing the right thing. Think of it like the           *)
    (* test harness.                                                       *)
    (***********************************************************************)
    \* Represents all the write requests and read responses sent to/from 
    \* the system.
    operations 


(***************************************************************************)
(* Represents every variable in this model.                                *)
(***************************************************************************)
vars == <<databaseState, blobStoreState, serverStates, operations>> 

(***************************************************************************)
(* You strongly type math with math. Here is where we say which types are  *)
(* allowed for all our variables. TypeOk is set as an Invariant, which     *)
(* means we expect it always to be true. It will fail if false,            *)
(* effectively giving us type checking.                                    *)
(* The declarations that follow are part of TypeOk, separated to make it   *)
(* clearer.                                                                *)
(***************************************************************************)


(***************************************************************************)
(* Allows all the values to also be UNSET, which is a distinct value not   *)
(* to be confused for the others.                                          *)
(***************************************************************************)
UserIdVal == USERIDS \union {"UNSET"}
MetadataVal == METADATAS \union {"UNSET"}
ImageVal == IMAGES \union {"UNSET"}


(***************************************************************************)
(* Describes all possible states a server can be in.                       *)
(***************************************************************************)
ServerStateVal == 
    [
        state: {
            \* current: 
            "waiting", \* next: StartWrite or StartRead
            \* after: StartWrite
            "started_write", \* next: WriteMetadata or FailWrite
            \* after: WriteMetadata
            "wrote_metadata", \* next: WriteBlobAndReturn or FailWrite
            \* after: StartRead
            "started_read", \* next: ReadMetadata
            \* after: ReadMetadata
            "read_metadata" \* next: ReadBlobAndReturn
        }, 
        userId: UserIdVal,
        metadata:  MetadataVal,
        image: ImageVal
    ]


(***************************************************************************)
(* Represents an action that occured on the API boundary. Used for         *)
(* observability.                                                          *)
(***************************************************************************)
OperationValue == [type: {"READ", "WRITE"}, 
                   userId: UserIdVal, 
                   metadata: MetadataVal, 
                   image:ImageVal]
                   
(***************************************************************************)
(* The full type specification for all variables in the system             *)
(***************************************************************************)
TypeOk ==
    (***********************************************************************)
    (* The database state contains a mapping of userIds to metadatas.      *)
    (* It can also be "UNSET", representing a case where there is no       *)
    (* metadata.                                                           *)
    (* Note: we make this specific to our problem. If this were a more     *)
    (* general problem, it might look like:                                *)
    (*      databaseState \in [KEYS -> RECORDS].                           *)
    (***********************************************************************)
    /\ databaseState \in [USERIDS -> MetadataVal]
    (***********************************************************************)
    (* The blob store state contains a mapping of userIds to images.       *)
    (* Note: we make this specific to our problem. If this was a more      *)
    (* general problem, it might look like:                                *)
    (*      blobStoreState \in [KEYS -> BLOBS].                            *)
    (***********************************************************************)
    /\ blobStoreState \in [USERIDS -> ImageVal]
    (***********************************************************************)
    (* The serverStates store the current states for each server, allowing *)
    (* us to build a state machine describing our system. Implemented as a *)
    (* mapping between servers and all their possible states.              *)
    (***********************************************************************)
    /\ serverStates \in [SERVERS -> ServerStateVal]
    /\ operations \in Seq(OperationValue)


(***************************************************************************)
(* When the model starts, everything begins unset. Unlike standard testing *)
(* every possible state will be explored, so we don't need to initialize   *)
(* for specific scenarios.                                                 *)
(***************************************************************************)
Init ==
    /\ databaseState = [u \in USERIDS |->  "UNSET"]
    /\ blobStoreState = [u \in USERIDS |->  "UNSET"]
    /\ serverStates = [s \in SERVERS |->  [state |-> "waiting",
                                           userId |-> "UNSET",
                                           metadata |-> "UNSET",
                                           image |-> "UNSET"
                                          ]]
    /\ operations = <<>>
    
(***************************************************************************)
(* State Machine: All of the states are functions of s (server), because   *)
(* the only actively modeled actors in this system are our servers, but    *)
(* there can be multiple working simultainiously.                          *)
(***************************************************************************)

StartWrite(s) ==
    \* Writing only starts when a server is waiting
    /\ serverStates[s].state = "waiting"
    \* This will try every combination of userId, metadata and image (one at 
    \* a time). We store this throughout the state lifecycle. Next states will
    \* refer to this
    /\ \E u \in USERIDS, m \in METADATAS, i \in IMAGES:
       \* serverStates' means the next state of serverStates
        /\ serverStates' = [serverStates EXCEPT \* update only server s 
                                ![s].state ="started_write", \* update state
                                \* set values for the upcoming write
                                ![s].userId = u, 
                                ![s].metadata = m,
                                ![s].image = i]
        \* Record the write for observability
        /\ operations' = Append(operations, 
                                \* This is created with "record" symantics,
                                \* which is why |-> not = is used
                                    [ 
                                       type |-> "WRITE",
                                       userId |-> u,
                                       metadata |-> m,
                                       image |-> i
                                    ])
    \* We need to list every unchanged variable. 
    \* Not changing is a behavior too.
    /\ UNCHANGED <<databaseState, blobStoreState>> 


WriteMetadata(s) == \* Represents a successful database write
    \* Established an alias to make code more compact
    LET currentState == serverStates[s] 
    IN
    \* Metadata writing happens directly after write is started
    /\ currentState.state = "started_write"
    \* Database is transactional/consistent. We can therefore model this
    \* happening in one step
    /\ databaseState' = [databaseState EXCEPT 
                            ![currentState.userId] = currentState.metadata ]
    /\ serverStates' = [serverStates EXCEPT \* This is how the state advances
                            ![s].state ="wrote_metadata"]
    /\ UNCHANGED <<blobStoreState, operations>>

WriteBlobAndReturn(s) == \* Represents a successful blob store write
    LET currentState == serverStates[s] 
    IN
        \* Metadata writing happens directly after write is started
        /\ currentState.state = "wrote_metadata"
        \* Blob store has read after write consistency. We can therefore 
        \* model it happening in one step
        /\ blobStoreState' = [blobStoreState EXCEPT 
                                ![currentState.userId] = currentState.image ]
        /\ serverStates' = [serverStates EXCEPT \* update only server s
                                \* Process done once blob is written
                                ![s].state ="waiting"]
        /\ UNCHANGED <<databaseState, operations>>

FailWrite(s) ==
    (***********************************************************************)
    (* In our model, a server can only fail if it is writing. We don't     *)
    (* need to do this, but it cuts down state space we don't care about.  *)
    (* We are worried about writes failing in a bad spot causing errors in *)
    (* future reads and writes. We don't model spontaneous read failures.  *)
    (***********************************************************************)
    \* Will only get to this state if writing
    /\ serverStates[s].state \in {"started_write", "wrote_metadata"}
    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET"]
    (***********************************************************************)
    (* Nothing happens with the database and blob store. Everything this   *)
    (* server did stays done, anything left undone stays undone.           *)
    (***********************************************************************)
    /\ UNCHANGED <<databaseState, blobStoreState, operations>> 

(***************************************************************************)
(* We model reading in detail because reading and writing are occurring at *)
(* the same time, and may interact with each other in unexpected ways.     *)
(***************************************************************************)

StartRead(s) ==
    \* Reading only starts when a server is waiting
    /\ serverStates[s].state = "waiting"
    /\ \E u \in USERIDS: \* When we start reading we pick a user id
                serverStates' = [serverStates EXCEPT \* update only server s
                                    ![s].state ="started_read",
                                    ![s].userId =u]
    \* Reading doesn't changed stored state
    /\ UNCHANGED <<databaseState, blobStoreState>> 
    /\ UNCHANGED operations

ReadMetadata(s) ==
    LET currentState == serverStates[s] 
    IN
    \* Once the read has started, the first thing we do is Read Metadata
    /\ currentState.state = "started_read"
    /\ serverStates' = 
            [serverStates EXCEPT \* update only server s 
                ![s].state ="read_metadata",
                (***********************************************)
                (* Assembles the read request from whatever is *)
                (* in the database for that user.              *)
                (***********************************************)
                ![s].metadata = databaseState[currentState.userId]]
                                            
    \* Reading doesn't changed stored state
    /\ UNCHANGED <<databaseState, blobStoreState>>
    /\ UNCHANGED operations

ReadBlobAndReturn(s) ==
    LET currentState == serverStates[s] 
    IN
    \* Blob is read after metadata is read
    /\ currentState.state = "read_metadata"
    /\ serverStates' = [serverStates EXCEPT \* update only server s 
                            ![s].state ="waiting",
                            (***********************************************)
                            (* Assembles the read request from whatever is *)
                            (* in the database for that user.              *)
                            (***********************************************)
                            ![s].image = blobStoreState[currentState.userId]]
                                            
    /\ operations' = Append(operations,
                            (***********************************************)
                            (* Read returns the state it built up during   *)
                            (* the read process.                           *)
                            (***********************************************)
                            [ 
                               type |-> "READ",
                               userId |-> currentState.userId,
                               metadata |-> currentState.metadata,
                               image |-> blobStoreState[currentState.userId]
                            ])
    \* Reading doesn't changed stored state
    /\ UNCHANGED <<databaseState, blobStoreState>>



(***************************************************************************)
(* The Next section determines what states will be chosen on every step.   *)
(***************************************************************************)
Next ==
    \* For every step, pick a server and have it advance one state
    \E s \in SERVERS: 
        \/ StartWrite(s)
        \/ WriteMetadata(s)
        \/ WriteBlobAndReturn(s)
        \/ FailWrite(s)
        \/ StartRead(s)
        \/ ReadMetadata(s)
        \/ ReadBlobAndReturn(s)

(***************************************************************************)
(* The Spec describes what the describe system DOES.                       *)
(* First it starts in the Init state.                                      *)
(* Then for every step use Next state: represented as []Next.              *)
(* In temporal logic [] means "for all states."                            *)
(* However let's imagine this is part of a larger system; sometimes this   *)
(* system will do nothing. That is represented by [Next]_vars, meaning:    *)
(* Next \/ UNCHANGED vars.                                                 *)
(* See learning material for a better explaination of temporal logic       *)
(* operators.                                                              *)
(* Note: The spec in this case describes what the system DOES, not what it *)
(* should do. Basically this is our system under test, and we describe     *)
(* Invariants (below) and properties (discussed later) to alert us if the  *)
(* system does something wrong/unexpected                                  *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars


(***************************************************************************)
(* Invariants: These are things that should always be true about the       *)
(* system. If they become false during any step, an error will occur with  *)
(* a trace that shows you the series of steps that let it to be violated.  *)
(* This is very powerful.                                                  *)
(* The first invariant we saw was TypeOk: the types are expected to always *)
(* conform to the expected type system, and if not we want to know why.    *)
(***************************************************************************)

ConsistentReads ==
    \* If there are no operations, they are consistent
    \/ operations = <<>>
    \/ \A i \in 1..Len(operations): \* For every read operation
        LET readOp == operations[i] IN
        \/  /\ readOp.type = "READ"
            \* There must exist a write operation
            /\  \/ \E j \in 1..i: 
                    LET writeOp == operations[j] IN
                    /\ writeOp.type = "WRITE"
                    \* With the same data
                    /\ readOp.userId = writeOp.userId
                    /\ readOp.metadata = writeOp.metadata
                    /\ readOp.image = writeOp.image
                \/ \* Ignore unset reads
                    /\ readOp.metadata = "UNSET"
                    /\ readOp.image = "UNSET"
        \/ readOp.type = "WRITE" \* Ignore writes
         


(***************************************************************************)
(* One of the best things about invariants is that if they were ever going *)
(* to be tripped, you'll hear about it. Unlike testing, where sometimes a  *)
(* confluence of events leads to a test passing when it shouldn't, the     *)
(* model checker will try every possible state, so if it ever messes up,   *)
(* you'll know.                                                            *)
(***************************************************************************)

(***************************************************************************)
(* This is used for model checker configuration so the simulation doesn't  *)
(* go on forever.                                                          *)
(***************************************************************************)
StopAfter3Operations ==
    Len(operations) <= 3

=============================================================================
