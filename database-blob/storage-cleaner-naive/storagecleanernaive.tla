---------------------------- MODULE storagecleanernaive ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    USERIDS,
    SERVERS,
    METADATAS,
    IMAGES,
    UUIDS,
    \* Added to
    CLEANERS

VARIABLES
    databaseState,
    blobStoreState,
    serverStates,
    cleanerStates, \* CleanerStates[storageCleanerId]

    operations 


vars == <<databaseState, blobStoreState, 
            serverStates, operations, cleanerStates>> 

cleanerVars == <<cleanerStates>>

(***************************************************************************)
(* Strong Typing                                                           *)
(***************************************************************************)

UserIdVal == USERIDS \union {"UNSET"}
MetadataVal == METADATAS \union {"UNSET"}
ImageVal == IMAGES \union {"UNSET"}
UUIDVal == UUIDS \union {"UNSET"} \* added UUID type

DatabaseRecord == [
    metadata: MetadataVal,
    imageId: UUIDVal
]

(***************************************************************************)
(* Describes all possible states a server can be in. Unchanged since last  *)
(* example)                                                                *)
(***************************************************************************)
ServerStateVal == 
    [
        state: {
            \* current: 
            "waiting", \* next: ServerStartWrite or ServerStartRead
            \* after: ServerStartWrite
            "started_write", \* next: ServerWriteBlob or ServerFailWrite
            \* after: ServerWriteBlob
            "wrote_blob", \* next: ServerWriteMetadataAndReturn or ServerFailWrite
            \* after: ServerStartRead
            "started_read", \* next: ServerReadMetadata
            \* after: ServerReadMetadata, ServerReadMetadataAndReturnEmpty
            "read_metadata" \* next: ServerReadBlobAndReturn
        }, 
        userId: UserIdVal,
        metadata:  MetadataVal,
        imageId: UUIDVal, \* Need to track imageId to perform a lookup
        image: ImageVal
    ]

(***************************************************************************)
(* Describes all possible states a server can be in. Unchanged since last  *)
(* example)                                                                *)
(***************************************************************************)
CleanerStateVal == 
    [
        state: {
            \* current: 
            "waiting", \* next: CleanerStartGetBlobKeys
            \* after: waiting
            "got_blob_keys", \* next: CleanerGetUnusedKeys or CleanerFail
            \* after: got_blob_keys
            "got_unused_keys", \* next: CleanerDeleteKeys or CleanerFail
            \* after: got_unused_keys
            \* next: CleanerDeleteKeys, CleanerFinished, or waiting
            "deleting_keys" 
        },
        blobKeys: SUBSET UUIDS,
        unusedBlobKeys: SUBSET UUIDS
    ]

\* This is an observability value, and we are still measuring the same thing
\* No changes are needed
OperationValue == [type: {"READ", "WRITE"}, 
                   userId: UserIdVal, 
                   metadata: MetadataVal, 
                   image:ImageVal]

TypeOk ==
    /\ databaseState \in [USERIDS -> DatabaseRecord]
    /\ blobStoreState \in [UUIDS -> ImageVal]
    /\ serverStates \in [SERVERS -> ServerStateVal]
    \* Added cleaner states to track status of cleaners
    /\ cleanerStates \in [CLEANERS -> CleanerStateVal]
    /\ operations \in Seq(OperationValue)


Init ==
    /\ databaseState = 
            [u \in USERIDS |-> [metadata |-> "UNSET", imageId |-> "UNSET"]]
    /\ blobStoreState = [u \in UUIDS |->  "UNSET"]
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
    
(***************************************************************************)
(* State Machine: All of the states are functions of s (server), because   *)
(* the only actively modelled actors in this system are our servers, but   *)
(* there can be multiple working simultainiously.                          *)
(***************************************************************************)

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
    \* Cleaner state needs to be added as unchanged for all server operations
    /\ UNCHANGED <<databaseState, blobStoreState, cleanerStates>> 


ServerWriteBlob(s) ==
    LET currentState == serverStates[s] 
    IN
    /\ currentState.state = "started_write"
    /\ \E id \in UUIDS:
        /\ blobStoreState[id] = "UNSET" \* 
        /\ blobStoreState' = [blobStoreState EXCEPT 
                                ![id] = currentState.image ]
        /\ serverStates' = [serverStates EXCEPT
                                ![s].state ="wrote_blob",
                                ![s].imageId = id]
    /\ UNCHANGED <<databaseState, operations>>
    /\ UNCHANGED cleanerVars


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

\* If database record is present
ServerReadMetadata(s) ==
    LET currentState == serverStates[s] 
    IN
    /\ currentState.state = "started_read"
    \* Represents reading the metadata while the database record is set
    /\ databaseState[currentState.userId].metadata # "UNSET"
    /\ serverStates' = 
        [serverStates EXCEPT
            ![s].state ="read_metadata",
            ![s].metadata = databaseState[currentState.userId].metadata,
            \* Reads imageId from database
            ![s].imageId = databaseState[currentState.userId].imageId]
    /\ UNCHANGED <<databaseState, blobStoreState>>
    /\ UNCHANGED operations
    /\ UNCHANGED cleanerVars

\* If database record is not present
ServerReadMetadataAndReturnEmpty(s) ==
    LET currentState == serverStates[s] 
    IN
    /\ currentState.state = "started_read"
    \* Represents reading the metadata while the database record is unset
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
    
ServerReadBlobAndReturn(s) ==
    LET currentState == serverStates[s] 
    IN
    /\ currentState.state = "read_metadata"                               
    /\ operations' = Append(operations,
                            [ 
                               type |-> "READ",
                               userId |-> currentState.userId,
                               metadata |-> currentState.metadata,
                               image |-> blobStoreState[currentState.imageId]
                            ])
    /\ serverStates' = [serverStates EXCEPT
                            ![s].state ="waiting",
                            ![s].userId ="UNSET",
                            ![s].metadata = "UNSET",
                            ![s].image = "UNSET",
                            ![s].imageId = "UNSET"]
    /\ UNCHANGED <<databaseState, blobStoreState>>
    /\ UNCHANGED cleanerVars

(***************************************************************************)
(* Cleaner States                                                          *)
(***************************************************************************)

CleanerStartGetBlobKeys(c) ==
    LET current == cleanerStates[c] IN
    \* Starts only from waiting
    /\ current.state = "waiting"
    /\ cleanerStates' = [
        cleanerStates EXCEPT
            ![c].state = "got_blob_keys",
            \* All keys that are set in blockstore
            ![c].blobKeys = {k \in UUIDS: blobStoreState[k] # "UNSET"}
        ]
    /\ UNCHANGED <<serverStates, databaseState, blobStoreState, operations>>

CleanerGetUnusedKeys(c) ==
    LET current == cleanerStates[c] IN
    \* From blob keys, get unused keys from database
    /\ current.state = "got_blob_keys"
    /\ cleanerStates' = [
        cleanerStates EXCEPT
            ![c].state = "got_unused_keys",
            ![c].unusedBlobKeys = 
                {k \in current.blobKeys: \* Keys in blob keys
                    \A u \in USERIDS: \* That are not in the database
                        databaseState[u].imageId # k}
        ]
    /\ UNCHANGED <<serverStates, databaseState, blobStoreState, operations>>

CleanerDeletingKeys(c) ==
    LET current == cleanerStates[c] IN
    \* When we have unused keys, keep deleting
    /\ current.state \in {"got_unused_keys", "deleting_keys"}
    /\ Cardinality(current.unusedBlobKeys) # 0
    /\ \E k \in current.unusedBlobKeys: \* pick a key to delete
        /\ blobStoreState' = [blobStoreState EXCEPT ![k] = "UNSET"]
        /\ cleanerStates' = [
            cleanerStates EXCEPT
                \* remove the key from set
                ![c].unusedBlobKeys = current.unusedBlobKeys \ {k}
            ]
    /\ UNCHANGED <<serverStates, databaseState, operations>>

CleanerFinished(c) ==
    LET current == cleanerStates[c] IN
    \* When we have no more unused keys to delete, finish
    /\ current.state = "deleting_keys"
    /\ Cardinality(current.unusedBlobKeys) = 0
    /\ cleanerStates' = [
        cleanerStates EXCEPT
            ![c].state = "waiting",
            ![c].blobKeys = {},
            ![c].unusedBlobKeys = {}
        ]
    /\ UNCHANGED <<serverStates, databaseState, blobStoreState, operations>>

CleanerFail(c) ==
    LET current == cleanerStates[c] IN
    \* Cleaner can fail from any active state
    /\ current.state \in {"got_blob_keys", "got_unused_keys", "deleting_keys"}
    (************************************************************************)
    (* Failure represented by cleaner losing state. Any partial operations  *)
    (* stay partially finished.                                             *)
    (************************************************************************)
    /\ cleanerStates' = [
        cleanerStates EXCEPT
            ![c].state = "waiting",
            ![c].blobKeys = {},
            ![c].unusedBlobKeys = {}
        ]
    /\ UNCHANGED <<serverStates, databaseState, blobStoreState, operations>>

(***************************************************************************)
(* Specification / Next                                                    *)
(***************************************************************************)
Next ==
    \* For every step, we either trigger a server or cleaner to take a step
    \/  \E s \in SERVERS: 
            \/ ServerStartWrite(s)
            \/ ServerWriteBlob(s)
            \/ ServerWriteMetadataAndReturn(s)
            \/ ServerFailWrite(s)
            \/ ServerStartRead(s)
            \/ ServerReadMetadata(s)
            \/ ServerReadMetadataAndReturnEmpty(s)
            \/ ServerReadBlobAndReturn(s)
    \/ \E c \in CLEANERS: \* all the steps a cleaner can take
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
        /\ blobStoreState[k] # "UNSET"
        \* And not in database
        /\ \A u \in USERIDS:
            databaseState[u].imageId # k



\* At some point in the future there will be no orphan files
\* If it's true ever, it is True
EventuallyNoOrphanFiles == <>NoOrphanFiles

\* Always, at some point in the future, there will be no orphan files
\* This is how we test eventual consistency. It can't just happen once
\* It must always happen
AlwaysEventuallyNoOrphanFiles == []EventuallyNoOrphanFiles

StopAfter3Operations ==
    Len(operations) <= 3

StopAfter5Operations ==
    Len(operations) <= 5

=============================================================================
