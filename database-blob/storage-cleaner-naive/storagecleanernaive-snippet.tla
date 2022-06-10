---------------------------- MODULE storagecleanernaive ----------------------------

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
    /\ \E k \in current.unusedBlobKeys: \* Pick a key to delete
        /\ blobStoreState' = [blobStoreState EXCEPT ![k] = "UNSET"]
        /\ cleanerStates' = [
            cleanerStates EXCEPT
                \* Remove the key from set
                ![c].unusedBlobKeys = current.unusedBlobKeys \ {k}
            ]
    /\ UNCHANGED <<serverStates, databaseState, operations>>

CleanerFinished(c) ==
    LET current == cleanerStates[c] IN
    /\ current.state = "deleting_keys"
    \* When we have no more unused keys to delete, finish
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
    \/ \E c \in CLEANERS: \* All the steps a cleaner can take
            \/ CleanerStartGetBlobKeys(c)
            \/ CleanerGetUnusedKeys(c)
            \/ CleanerDeletingKeys(c)
            \/ CleanerFinished(c)
            \/ CleanerFail(c)



Spec == Init /\ [][Next]_vars


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

NoOrphanFiles ==
    \* There does not exist a key
    ~\E k \in UUIDS:
        \* That is in the block store
        /\ blobStoreState[k] # "UNSET"
        \* And not in the database
        /\ \A u \in USERIDS:
            databaseState[u].imageId # k

=============================================================================