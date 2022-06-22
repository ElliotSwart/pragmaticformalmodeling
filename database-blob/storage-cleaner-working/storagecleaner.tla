---------------------------- MODULE storagecleaner ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    USERIDS,
    SERVERS,
    METADATAS,
    IMAGES,
    UUIDS,
    CLEANERS

VARIABLES
    (***********************************************************************)
    (* Implementation variables                                            *)
    (***********************************************************************)
    databaseState,
    blobStoreState,
    serverStates,
    cleanerStates,

    \* We just added a time variable here
    time, \* Natural number representing the number of hours that have passed

    (***********************************************************************)
    (* Observability variables                                             *)
    (***********************************************************************)
    operations,
    usedIds,
    
    (***********************************************************************)
    (* Temporal property variable: used to change state space on failure   *)
    (***********************************************************************)
    failed

helperVars == <<time, operations, usedIds, failed>>

vars == <<databaseState, blobStoreState, 
            serverStates, operations, cleanerStates, time, usedIds, failed>> 

cleanerVars == <<cleanerStates>>

(***************************************************************************)
(* Strong Typing                                                           *)
(***************************************************************************)

UserIdVal == USERIDS \union {"UNSET"}
MetadataVal == METADATAS \union {"UNSET"}
ImageVal == IMAGES \union {"UNSET"}
UUIDVal == UUIDS \union {"UNSET"}

DatabaseRecord == [
    metadata: MetadataVal,
    imageId: UUIDVal
]


BlobStoreRecord == [
    image: ImageVal,
    created: Nat
]  \union {[
    status |-> "UNSET",
    image |-> "UNSET"
]}


ServerStateVal == 
    [
        state: {
            "waiting",
            "started_write",
            "wrote_blob",
            "started_read",
            "read_metadata"
        }, 
        userId: UserIdVal,
        metadata:  MetadataVal,
        imageId: UUIDVal,
        image: ImageVal,
        start: Nat \* added to track when a request starts
    ]

CleanerStateVal == 
    [
        state: {
            "waiting", 
            "got_blob_keys", 
            "got_unused_keys",
            "deleting_keys" 
        },
        \* This will be used to introduce a delay
        unusedKeyTime: Nat,
        blobKeys: SUBSET UUIDS,
        unusedBlobKeys: SUBSET UUIDS
    ]


OperationValue == [type: {"READ", "WRITE"}, 
                   userId: UserIdVal, 
                   metadata: MetadataVal, 
                   image:ImageVal]

TypeOk ==
    /\ databaseState \in [USERIDS -> DatabaseRecord]
    /\ blobStoreState \in [UUIDS -> BlobStoreRecord]
    /\ serverStates \in [SERVERS -> ServerStateVal]
    /\ cleanerStates \in [CLEANERS -> CleanerStateVal]
    /\ operations \in Seq(OperationValue)
    /\ time \in Nat
    /\ usedIds \in SUBSET UUIDS
    /\ failed \in Nat

Init ==
    /\ databaseState = 
            [u \in USERIDS |-> [metadata |-> "UNSET", imageId |-> "UNSET"]]
    /\ blobStoreState = 
            [u \in UUIDS |->  [status |-> "UNSET", image |-> "UNSET"]]
    /\ serverStates = [s \in SERVERS |->  [state |-> "waiting",
                                           userId |-> "UNSET",
                                           metadata |-> "UNSET",
                                           imageId |-> "UNSET",
                                           image |-> "UNSET",
                                           \* will be set on start states
                                           start |-> 0 
                                          ]]
    /\ cleanerStates = [c \in CLEANERS |-> [
                                                    state |-> "waiting",
                                                    blobKeys |-> {},
                                                    unusedBlobKeys |-> {},
                                                    unusedKeyTime |-> 0
                                                  ]]
    /\ operations = <<>>
    /\ time = 0 \* Time starts at 0
    /\ usedIds = {}
    /\ failed = 0

(***************************************************************************)
(* State Machine:                                                          *)
(***************************************************************************)

TimePasses ==
    /\ time' = time + 1
    /\ UNCHANGED <<serverStates, databaseState, 
                        blobStoreState, cleanerStates>>
    /\ UNCHANGED <<operations, usedIds, failed>>


(***************************************************************************)
(* Server Restart                                                          *)
(***************************************************************************)

ServerRestart(s) ==
    LET currentState == serverStates[s] IN 
    LET terminationTime == (currentState.start + 1) IN
    /\ currentState.state # "waiting" \* Server must be active
    \* This is the only state a server can reach if past termination time
    /\ time => terminationTime
    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET",
                                ![s].imageId = "UNSET"]
    /\ UNCHANGED <<databaseState, blobStoreState, cleanerVars>>
    /\ UNCHANGED helperVars

(***************************************************************************)
(* Server Writes                                                           *)
(***************************************************************************)

ServerStartWrite(s) ==
    /\ serverStates[s].state = "waiting"
    /\ \E u \in USERIDS, m \in METADATAS, i \in IMAGES:
        /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="started_write",
                                ![s].userId = u, 
                                ![s].metadata = m,
                                ![s].image = i,
                                \* The time a write request starts
                                ![s].start = time
                                ]
        /\ operations' = Append(operations, 
                                    [ 
                                       type |-> "WRITE",
                                       userId |-> u,
                                       metadata |-> m,
                                       image |-> i
                                    ])
    /\ UNCHANGED <<databaseState, blobStoreState, cleanerStates>>
    /\ UNCHANGED <<time, usedIds, failed>>

ServerWriteBlob(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ currentState.state = "started_write"
    /\ \E id \in UUIDS:
        /\ id \notin usedIds
        /\ blobStoreState[id] = [status |-> "UNSET", image |-> "UNSET"]
        /\ blobStoreState' = [blobStoreState EXCEPT 
                                ![id] = [
                                    image |-> currentState.image,
                                    created |-> time
                                    ]]
        /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="wrote_blob",
                                ![s].imageId = id]
        /\ usedIds' = usedIds \union {id}
    /\ UNCHANGED <<databaseState, cleanerVars>>
    /\ UNCHANGED  <<time, operations, failed>>


ServerWriteMetadataAndReturn(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime
    /\ currentState.state = "wrote_blob"
    /\ databaseState' = [databaseState EXCEPT 
                            ![currentState.userId] = [
                                metadata |-> currentState.metadata, 
                                imageId |-> currentState.imageId] ]

    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET",
                                ![s].imageId = "UNSET"]
    /\ UNCHANGED <<blobStoreState, cleanerVars>>
    /\ UNCHANGED helperVars

ServerFailWrite(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ serverStates[s].state \in {"started_write", "wrote_blob"}
    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET",
                                ![s].imageId = "UNSET"]
    /\ UNCHANGED <<databaseState, blobStoreState,cleanerVars>>
    /\ UNCHANGED helperVars


(***************************************************************************)
(* Server Reads                                                            *)
(***************************************************************************)

ServerStartRead(s) ==
    LET currentState == serverStates[s] IN
    /\ serverStates[s].state = "waiting"
    /\ \E u \in USERIDS:
                serverStates' = [serverStates EXCEPT
                                    ![s].state ="started_read",
                                    ![s].userId = u,
                                    \* The time a read request starts
                                    ![s].start = time
                                    ]
   
    /\ UNCHANGED <<databaseState, blobStoreState, cleanerVars>> 
    /\ UNCHANGED helperVars


ServerReadMetadata(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ currentState.state = "started_read"
    /\ databaseState[currentState.userId].metadata # "UNSET"
    /\ serverStates' = 
        [serverStates EXCEPT
            ![s].state ="read_metadata",
            ![s].metadata = databaseState[currentState.userId].metadata,
            ![s].imageId = databaseState[currentState.userId].imageId]
    /\ UNCHANGED <<databaseState, blobStoreState, cleanerVars>>
    /\ UNCHANGED helperVars


ServerReadMetadataAndReturnEmpty(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ currentState.state = "started_read"
    /\ databaseState[currentState.userId].metadata = "UNSET"
    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET",
                                ![s].imageId = "UNSET"]
                                            
    /\ operations' = Append(operations,
                            [ 
                               type |-> "READ",
                               userId |-> currentState.userId,
                               metadata |-> "UNSET",
                               image |-> "UNSET"
                            ])
    /\ UNCHANGED <<databaseState, blobStoreState, cleanerVars>>
    /\ UNCHANGED <<usedIds, time, failed>>
    
ServerReadBlobAndReturn(s) ==
    LET currentState == serverStates[s] IN
    LET terminationTime == (currentState.start + 1) IN
    /\ time < terminationTime \* Can only start this state if server is live
    /\ currentState.state = "read_metadata"                               
    /\ operations' = Append(operations,
                            [ 
                               type |-> "READ",
                               userId |-> currentState.userId,
                               metadata |-> currentState.metadata,
                               image |-> blobStoreState[currentState.imageId].image
                            ])
    /\ serverStates' = [serverStates EXCEPT
                            ![s].state ="waiting",
                            ![s].userId ="UNSET",
                            ![s].metadata = "UNSET",
                            ![s].image = "UNSET",
                            ![s].imageId = "UNSET"]
    /\ UNCHANGED <<databaseState, blobStoreState, cleanerVars>>
    /\ UNCHANGED <<usedIds, time, failed>>

(***************************************************************************)
(* Cleaner States                                                          *)
(***************************************************************************)

(***************************************************************************)
(* This is the main change in the logic.                                   *)
(***************************************************************************)
CleanerStartGetBlobKeys(c) ==
    LET current == cleanerStates[c] IN
    /\ current.state = "waiting"
    /\ cleanerStates' = [
        cleanerStates EXCEPT
            ![c].state = "got_blob_keys",
            \* All keys in blockstore
            ![c].blobKeys = {
                k \in UUIDS:
                    LET earliestDeletionTime == blobStoreState[k].created + 2 IN
                    \* That are not unset
                    /\ blobStoreState[k] # [
                        status |-> "UNSET", 
                        image |-> "UNSET"] 
                    \* It must be created 2 or more hours ago
                    /\ earliestDeletionTime =< time
            }
        ]
    /\ UNCHANGED <<serverStates, databaseState, 
                        blobStoreState>>
    /\ UNCHANGED helperVars

CleanerGetUnusedKeys(c) ==
    LET current == cleanerStates[c] IN
    /\ current.state = "got_blob_keys"
    /\ cleanerStates' = [
        cleanerStates EXCEPT
            ![c].state = "got_unused_keys",
            ![c].unusedBlobKeys = 
                {k \in current.blobKeys:
                    \A u \in USERIDS:
                        databaseState[u].imageId # k},
            \* Mark the time the unused keys were retrieved
            ![c].unusedKeyTime = time
        ]
    /\ UNCHANGED <<serverStates, databaseState, 
                    blobStoreState>>
    /\ UNCHANGED helperVars

CleanerDeletingKeys(c) ==
    LET current == cleanerStates[c] IN
    \* Keys get deleted a minimum 1 hour after they are valid. Giving reads
    \* a the time to die.
    LET earliestDeleteTime == current.unusedKeyTime + 1 IN
    /\ time >= earliestDeleteTime
    /\ current.state \in {"got_unused_keys", "deleting_keys"}
    /\ Cardinality(current.unusedBlobKeys) # 0
    /\ \E k \in current.unusedBlobKeys: \* pick a key to delete
        /\ blobStoreState' = 
            [blobStoreState EXCEPT 
                ![k] = [status |-> "UNSET", image |-> "UNSET"]]
        /\ cleanerStates' = [
            cleanerStates EXCEPT
                ![c].unusedBlobKeys = current.unusedBlobKeys \ {k}
            ]
    /\ UNCHANGED <<serverStates, databaseState>>
    /\ UNCHANGED helperVars

CleanerFinished(c) ==
    LET current == cleanerStates[c] IN
    /\ current.state = "deleting_keys"
    /\ Cardinality(current.unusedBlobKeys) = 0
    /\ cleanerStates' = [
        cleanerStates EXCEPT
            ![c].state = "waiting",
            ![c].blobKeys = {},
            ![c].unusedBlobKeys = {}
        ]
    /\ UNCHANGED <<serverStates, databaseState, 
                        blobStoreState>>
    /\ UNCHANGED helperVars

CleanerFail(c) ==
    LET current == cleanerStates[c] IN
    /\ current.state \in {"got_blob_keys", "got_unused_keys", "deleting_keys"}
    /\ cleanerStates' = [
        cleanerStates EXCEPT
            ![c].state = "waiting",
            ![c].blobKeys = {},
            ![c].unusedBlobKeys = {}
        ]
    \* change state space on failed
    /\ failed' = failed + 1
    /\ UNCHANGED <<serverStates, databaseState, 
                        blobStoreState>>
    /\ UNCHANGED <<time, operations, usedIds>>

(***************************************************************************)
(* Specification / Next                                                    *)
(***************************************************************************)

CleanerSteps == 
    \E c \in CLEANERS:
        \/ CleanerStartGetBlobKeys(c)
        \/ CleanerGetUnusedKeys(c)
        \/ CleanerDeletingKeys(c)
        \/ CleanerFinished(c)
        \/ CleanerFail(c)

Next ==
    \* Time can pass now
    \/ TimePasses
    \/  \E s \in SERVERS: 
            \/ ServerStartWrite(s)
            \/ ServerWriteBlob(s)
            \/ ServerWriteMetadataAndReturn(s)
            \/ ServerFailWrite(s)
            \/ ServerStartRead(s)
            \/ ServerReadMetadata(s)
            \/ ServerReadMetadataAndReturnEmpty(s)
            \/ ServerReadBlobAndReturn(s)
    \/ CleanerSteps


Spec == /\ Init 
        /\ [][Next]_vars 
        /\ WF_vars(CleanerSteps) \* The cleaner will always get to run


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

\* Note that the success criteria hasn't changed this whole time

ConsistentReads ==
    \* If there are no operations, they are consistent
    \/ operations = <<>>
    \/ \A i \in 1..Len(operations): \* For every read operation
        LET readOp == operations[i] IN
        \/  /\ readOp.type = "READ"
            \* There must exists a write operation
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

NoOrphanFiles ==
    \* There does not exist a key
    ~\E k \in UUIDS:
        \* That is in the block store
        /\ blobStoreState[k] # [status |-> "UNSET", image |-> "UNSET"]
        \* And not in database
        /\ \A u \in USERIDS:
            databaseState[u].imageId # k

(***************************************************************************)
(* This is used for model checker configuration so that simulation         *)
(* doesn't go on forever                                                   *)
(***************************************************************************)


\* At some point in the future there will be no orphan files
\* If it's true ever, it is True
EventuallyNoOrphanFiles == <>NoOrphanFiles

\* Always, at some point in the future, there will be no orphan files
\* This is how we test eventual consistency. It can't just happen once
\* It must always happen
AlwaysEventuallyNoOrphanFiles == []EventuallyNoOrphanFiles

StopAfter3Operations ==
    /\ Len(operations) <= 3
    /\ time <= 3

StopAfter5Operations ==
    Len(operations) <= 5

=============================================================================
