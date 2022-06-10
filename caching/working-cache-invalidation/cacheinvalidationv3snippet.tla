----------------------------- MODULE cacheinvalidationv3 -----------------------------

CacheHandleInvalidationMessage == 
    /\ \E message \in invalidationQueue: 
        /\ \/ /\ cache[message.key] \in CacheHit
              \* Message needs to be newer than the cache
              /\ cache[message.key].version < message.version
           \* Or not in the cache, but with a pending fill request
           \/ /\ cache[message.key] \in CacheMiss
              /\ cacheFillStates[message.key].state # "inactive"
        \* Update item in cache
        /\ cache' = [cache EXCEPT 
                        ![message.key] = [
                            type |-> "hit",
                            \* Update to version in invalidation message
                            version |-> message.version
                        ]]
        \* Remove message from queue because handled
        /\ invalidationQueue' = invalidationQueue \ {message}

    /\ UNCHANGED <<cacheFillStates, database, counter>>

CacheIgnoreInvalidationMessage == 
    /\ \E message \in invalidationQueue: \* Dequeue invalidation queue in any order
        \* Ignore invalidation messages for messages not in cache
        /\ \/ /\ cache[message.key] \in CacheMiss
              \* and a fill is not occurring
              /\ cacheFillStates[message.key].state = "inactive"
           \* Or when the cache already has the same or larger version
           \/ /\ cache[message.key] \notin CacheMiss
              /\ cache[message.key].version >= message.version
        \* Remove message from queue to ignore
        /\ invalidationQueue' = invalidationQueue \ {message}
    /\ counter' = counter + 1
    /\ UNCHANGED <<cacheFillStates, database, cache>>

CacheEvict(k) ==
    /\ cache[k] \in CacheHit
    \* A key with a pending request will not be evicted
    /\ cacheFillStates[k].state = "inactive"
    /\ cache' = [cache EXCEPT ![k] = [type |-> "miss"]]
    /\ counter' = counter + 1
    /\ UNCHANGED <<database, cacheFillStates, 
                    invalidationQueue>>

=============================================================================
\* Modification History
\* Last modified Wed Jun 15 13:08:32 MST 2022 by elliotswart
\* Created Tue Jun 14 20:36:02 MST 2022 by elliotswart
