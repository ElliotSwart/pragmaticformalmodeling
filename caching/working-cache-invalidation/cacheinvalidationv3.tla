----------------------------- MODULE cacheinvalidationv3 -----------------------------

EXTENDS Naturals

CONSTANTS
    KEYS


VARIABLES
    database,
    cache,
    cacheFillStates,
    invalidationQueue,
    counter \* Used to prevent repeated states for liveness conditions


INSTANCE cacherequirements

vars == <<database, cache, cacheFillStates, invalidationQueue, counter>>

InvalidationMessage == [key: KEYS, version: DataVersion]

CacheFillState == [state: {"inactive", "started", "respondedto"}, version: DataVersion]

CacheValue == CacheMiss \union CacheHit

TypeOk ==
    /\ database \in [KEYS -> DataVersion]
    /\ cache \in [KEYS -> CacheValue]
    /\ cacheFillStates \in [KEYS -> CacheFillState]
    /\ invalidationQueue \in SUBSET InvalidationMessage
    /\ counter \in Nat
    
Init ==
    /\ database = [k \in KEYS |-> 0]
    /\ cache = [k \in KEYS |-> [type |-> "miss"]]
    /\ cacheFillStates = [k \in KEYS |-> [
                                state |-> "inactive", 
                                version |-> 0]
                          ]
    /\ invalidationQueue = {}
    /\ counter = 0


DatabaseUpdate(k) ==
    LET updatedVersion == database[k] + 1 IN
    /\ database' = [database EXCEPT
                        ![k] = updatedVersion]
    /\ invalidationQueue' = invalidationQueue \union
                                {[key |-> k, version |-> updatedVersion]}
    /\ UNCHANGED <<cache, cacheFillStates, counter>>


CacheStartReadThroughFill(k) ==
    /\ cache[k] \in CacheMiss
    /\ cacheFillStates[k].state = "inactive"
    /\ cacheFillStates' = [cacheFillStates EXCEPT ![k].state = "started"]
    /\ UNCHANGED <<database, cache, invalidationQueue, counter>>


DatabaseRespondToCacheFill(k) ==
    /\ cacheFillStates[k].state = "started"
    /\ cacheFillStates' = [cacheFillStates EXCEPT 
                            ![k].state = "respondedto",
                            ![k].version = database[k] 
                           ]
    /\ UNCHANGED <<database, cache, invalidationQueue, counter>>


CacheFailFill(k) == 
    /\ cacheFillStates[k].state = "respondedto"
    /\ cacheFillStates' = [cacheFillStates EXCEPT
                            ![k].state = "inactive",
                            ![k].version = 0
                           ]
    /\ UNCHANGED <<database, cache, invalidationQueue, counter>>
    

CacheCompleteFill(k) == 
    /\ cacheFillStates[k].state = "respondedto"
    /\ \/ cache[k] \in CacheMiss
       \/ /\ cache[k] \notin CacheMiss
          /\ cache[k].version < cacheFillStates[k].version
    /\ cacheFillStates' = [cacheFillStates EXCEPT \* Reset to 0 
                            ![k].state = "inactive",
                            ![k].version = 0
                           ]
    /\ cache' = [cache EXCEPT
                        ![k] = [
                           type |-> "hit",
                           version |-> cacheFillStates[k].version
                        ]
                ]
    /\ UNCHANGED <<database, invalidationQueue, counter>>

CacheIgnoreFill(k) == 
    /\ cacheFillStates[k].state = "respondedto"
    /\ /\ cache[k] \in CacheHit
       /\ cache[k].version >= cacheFillStates[k].version
    /\ cacheFillStates' = [cacheFillStates EXCEPT
                            ![k].state = "inactive",
                            ![k].version = 0
                           ]
    /\ counter' = counter + 1
    /\ UNCHANGED <<cache, database, invalidationQueue>>

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

CacheFairness ==
    \E k \in KEYS:
        \/ CacheStartReadThroughFill(k) 
        \/ DatabaseRespondToCacheFill(k)
        \/ CacheCompleteFill(k)
        \/ CacheIgnoreFill(k)
        \/ CacheHandleInvalidationMessage
        \/ CacheIgnoreInvalidationMessage



(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Next == 
    \E k \in KEYS:
        \* Database states
        \/ DatabaseUpdate(k)
        \* Cache states
        \/ CacheStartReadThroughFill(k)
        \/ DatabaseRespondToCacheFill(k)
        \/ CacheCompleteFill(k)
        \/ CacheIgnoreFill(k)
        \/ CacheHandleInvalidationMessage
        \/ CacheIgnoreInvalidationMessage
        \/ CacheEvict(k)

Spec == Init /\ [][Next]_vars /\ WF_vars(CacheFairness)

=============================================================================
\* Modification History
\* Last modified Wed Jun 15 13:08:32 MST 2022 by elliotswart
\* Created Tue Jun 14 20:36:02 MST 2022 by elliotswart
