---------------------------- MODULE storagecleanerimproved ----------------------------
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
    operations 

vars == <<databaseState, blobStoreState, 
            serverStates, operations, cleanerStates, time>> 

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

\* A blob store record is modeled to store creation time
BlobStoreRecord == [
    image: ImageVal,
    created: Nat
]  \union {[
    status |-> "UNSET",
    image |-> "UNSET"
]} \* It can still be unset


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
        image: ImageVal
    ]

CleanerStateVal == 
    [
        state: {
            "waiting", 
            "got_blob_keys", 
            "got_unused_keys",
            "deleting_keys" 
        },
        blobKeys: SUBSET UUIDS,
        unusedBlobKeys: SUBSET UUIDS
    ]


OperationValue == [type: {"READ", "WRITE"}, 
                   userId: UserIdVal, 
                   metadata: MetadataVal, 
                   image:ImageVal]

TypeOk ==
    /\ databaseState \in [USERIDS -> DatabaseRecord]
    \* Blob store is updated to store records. Can be a record or unset
    /\ blobStoreState \in [UUIDS -> BlobStoreRecord]
    /\ serverStates \in [SERVERS -> ServerStateVal]
    /\ cleanerStates \in [CLEANERS -> CleanerStateVal]
    /\ operations \in Seq(OperationValue)
    /\ time \in Nat \* Time is represented as a natural number


Init ==
    /\ databaseState = 
            [u \in USERIDS |-> [metadata |-> "UNSET", imageId |-> "UNSET"]]
    /\ blobStoreState = 
            [u \in UUIDS |->  [status |-> "UNSET", image |-> "UNSET"]]
    /\ serverStates = [s \in SERVERS |->  [state |-> "waiting",
                                           userId |-> "UNSET",
                                           metadata |-> "UNSET",
                                           imageId |-> "UNSET",
                                           image |-> "UNSET"
                                          ]]
    /\ cleanerStates = [c \in CLEANERS |-> [
                                                    state |-> "waiting",
                                                    blobKeys |-> {},
                                                    unusedBlobKeys |-> {}
                                                  ]]
    /\ operations = <<>>
    /\ time = 0 \* Time starts at 0

(***************************************************************************)
(* State Machine                                                           *)
(***************************************************************************)

TimePasses ==
    /\ time' = time + 1
    /\ UNCHANGED <<serverStates, databaseState, blobStoreState, operations, 
                        cleanerStates>>

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
                                ![s].image = i]
        /\ operations' = Append(operations, 
                                    [ 
                                       type |-> "WRITE",
                                       userId |-> u,
                                       metadata |-> m,
                                       image |-> i
                                    ])

    /\ UNCHANGED <<databaseState, blobStoreState, cleanerStates>>
    /\ UNCHANGED time


ServerWriteBlob(s) ==
    LET currentState == serverStates[s] 
    IN
    /\ currentState.state = "started_write"
    /\ \E id \in UUIDS:
        /\ blobStoreState[id] = [status |-> "UNSET", image |-> "UNSET"]
        /\ blobStoreState' = [blobStoreState EXCEPT 
                                ![id] = [
                                    image |-> currentState.image,
                                    created |-> time
                                    ]]
        /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="wrote_blob",
                                ![s].imageId = id]
    /\ UNCHANGED <<databaseState, operations>>
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time

ServerWriteMetadataAndReturn(s) ==
    LET currentState == serverStates[s] 
    IN
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
        /\ UNCHANGED <<blobStoreState, operations>>
        /\ UNCHANGED cleanerVars
        /\ UNCHANGED time

ServerFailWrite(s) ==
    /\ serverStates[s].state \in {"started_write", "wrote_blob"}
    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET",
                                ![s].imageId = "UNSET"]
    /\ UNCHANGED <<databaseState, blobStoreState, operations>>
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time


(***************************************************************************)
(* Server Reads                                                            *)
(***************************************************************************)

ServerStartRead(s) ==
    /\ serverStates[s].state = "waiting"
    /\ \E u \in USERIDS:
                serverStates' = [serverStates EXCEPT
                                    ![s].state ="started_read",
                                    ![s].userId =u]
   
    /\ UNCHANGED <<databaseState, blobStoreState>> 
    /\ UNCHANGED operations
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time

ServerReadMetadata(s) ==
    LET currentState == serverStates[s] 
    IN
    /\ currentState.state = "started_read"
    /\ databaseState[currentState.userId].metadata # "UNSET"
    /\ serverStates' = 
        [serverStates EXCEPT
            ![s].state ="read_metadata",
            ![s].metadata = databaseState[currentState.userId].metadata,
            ![s].imageId = databaseState[currentState.userId].imageId]
    /\ UNCHANGED <<databaseState, blobStoreState>>
    /\ UNCHANGED operations
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time

ServerReadMetadataAndReturnEmpty(s) ==
    LET currentState == serverStates[s] 
    IN
    /\ currentState.state = "started_read"
    /\ databaseState[currentState.userId].metadata = "UNSET"
    /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="waiting",
                                ![s].userId ="UNSET",
                                ![s].metadata = "UNSET",
                                ![s].image = "UNSET",
                                ![s].imageId = "UNSET"]
                                            
    /\ operations' = Append(operations,
                            (***********************************************)
                            (* Returns an empty record                     *)
                            (***********************************************)
                            [ 
                               type |-> "READ",
                               userId |-> currentState.userId,
                               metadata |-> "UNSET",
                               image |-> "UNSET"
                            ])
    /\ UNCHANGED <<databaseState, blobStoreState>>
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time
    
ServerReadBlobAndReturn(s) ==
    LET currentState == serverStates[s] 
    IN
    /\ currentState.state = "read_metadata"                               
    /\ operations' = Append(operations,
                            [ 
                               type |-> "READ",
                               userId |-> currentState.userId,
                               metadata |-> currentState.metadata,
                               \* Looks up image by imageId
                               image |-> blobStoreState[currentState.imageId].image
                            ])
    /\ serverStates' = [serverStates EXCEPT
                            ![s].state ="waiting",
                            ![s].userId ="UNSET",
                            ![s].metadata = "UNSET",
                            ![s].image = "UNSET",
                            ![s].imageId = "UNSET"]
    /\ UNCHANGED <<databaseState, blobStoreState>>
    /\ UNCHANGED cleanerVars
    /\ UNCHANGED time

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
                    \* It must have been created 2 or more hours ago
                    /\ earliestDeletionTime =< time
            }
        ]
    /\ UNCHANGED <<serverStates, databaseState, blobStoreState, operations>>
    /\ UNCHANGED time

CleanerGetUnusedKeys(c) ==
    LET current == cleanerStates[c] IN
    /\ current.state = "got_blob_keys"
    /\ cleanerStates' = [
        cleanerStates EXCEPT
            ![c].state = "got_unused_keys",
            ![c].unusedBlobKeys = 
                {k \in current.blobKeys:
                    \A u \in USERIDS:
                        databaseState[u].imageId # k}
        ]
    /\ UNCHANGED <<serverStates, databaseState, blobStoreState, operations>>
    /\ UNCHANGED time

CleanerDeletingKeys(c) ==
    LET current == cleanerStates[c] IN
    /\ current.state \in {"got_unused_keys", "deleting_keys"}
    /\ Cardinality(current.unusedBlobKeys) # 0
    /\ \E k \in current.unusedBlobKeys:
        /\ blobStoreState' = 
            [blobStoreState EXCEPT 
                ![k] = [status |-> "UNSET", image |-> "UNSET"]]
        /\ cleanerStates' = [
            cleanerStates EXCEPT
                ![c].unusedBlobKeys = current.unusedBlobKeys \ {k}
            ]
    /\ UNCHANGED <<serverStates, databaseState, operations>>
    /\ UNCHANGED time

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
    /\ UNCHANGED <<serverStates, databaseState, blobStoreState, operations>>
    /\ UNCHANGED time

CleanerFail(c) ==
    LET current == cleanerStates[c] IN
    /\ current.state \in {"got_blob_keys", "got_unused_keys", "deleting_keys"}
    /\ cleanerStates' = [
        cleanerStates EXCEPT
            ![c].state = "waiting",
            ![c].blobKeys = {},
            ![c].unusedBlobKeys = {}
        ]
    /\ UNCHANGED <<serverStates, databaseState, blobStoreState, operations>>
    /\ UNCHANGED time

(***************************************************************************)
(* Specification / Next                                                    *)
(***************************************************************************)
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
    \/ \E c \in CLEANERS:
            \/ CleanerStartGetBlobKeys(c)
            \/ CleanerGetUnusedKeys(c)
            \/ CleanerDeletingKeys(c)
            \/ CleanerFinished(c)
            \/ CleanerFail(c)



Spec == Init /\ [][Next]_vars


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

\* Note that the success criteria hasn't changed this whole time

ConsistentReads ==
    \/ operations = <<>>
    \/ \A i \in 1..Len(operations):
        LET readOp == operations[i] IN
        \/  /\ readOp.type = "READ"
            /\  \/ \E j \in 1..i: 
                    LET writeOp == operations[j] IN
                    /\ writeOp.type = "WRITE"
                    /\ readOp.userId = writeOp.userId
                    /\ readOp.metadata = writeOp.metadata
                    /\ readOp.image = writeOp.image
                \/
                    /\ readOp.metadata = "UNSET"
                    /\ readOp.image = "UNSET"
        \/ readOp.type = "WRITE"

NoOrphanFiles ==
    ~\E k \in UUIDS:
        /\ blobStoreState[k] # [status |-> "UNSET", image |-> "UNSET"]
        /\ \A u \in USERIDS:
            databaseState[u].imageId # k

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

EventuallyNoOrphanFiles == <>NoOrphanFiles

AlwaysEventuallyNoOrphanFiles == []EventuallyNoOrphanFiles

StopAfter3Operations ==
    /\ Len(operations) <= 3
    /\ time <= 2

StopAfter5Operations ==
    Len(operations) <= 5

=============================================================================
