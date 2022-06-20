---------------------------- MODULE success ----------------------------

NoOrphanFiles ==
    \* There does not exist a key
    ~\E k \in UUIDS:
        \* That is in the block store
        /\ blobStoreState[k] # "UNSET"
        \* And not in database
        /\ \A u \in USERIDS:
            databaseState[u].imageId # k

AlwaysNoOrphanFiles == []NoOrphanFiles

\* At some point in the future there will be no orphan files
\* If it's true ever, it is True
EventuallyNoOrphanFiles == <>NoOrphanFiles

\* Always, at some point in the future, there will be no orphan files
\* This is how we test eventual consistency. It can't just happen once
\* It must always happen
AlwaysEventuallyNoOrphanFiles == []EventuallyNoOrphanFiles
=============================================================================