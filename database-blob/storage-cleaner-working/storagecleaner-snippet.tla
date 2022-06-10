---------------------------- MODULE storagecleaner ----------------------------

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
    /\ UNCHANGED <<serverStates, databaseState, blobStoreState, operations>>
    /\ UNCHANGED time

CleanerDeletingKeys(c) ==
    LET current == cleanerStates[c] IN
    \* Keys get deleted a minimum 1 hour after they are valid
    \* This gives reads time to die
    LET earliestDeleteTime == current.unusedKeyTime + 1 IN
    /\ time >= earliestDeleteTime
    /\ current.state \in {"got_unused_keys", "deleting_keys"}
    /\ Cardinality(current.unusedBlobKeys) # 0
    /\ \E k \in current.unusedBlobKeys: \* Pick a key to delete
        /\ blobStoreState' = 
            [blobStoreState EXCEPT 
                ![k] = [status |-> "UNSET", image |-> "UNSET"]]
        /\ cleanerStates' = [
            cleanerStates EXCEPT
                ![c].unusedBlobKeys = current.unusedBlobKeys \ {k}
            ]
    /\ UNCHANGED <<serverStates, databaseState, operations>>
    /\ UNCHANGED time

=============================================================================