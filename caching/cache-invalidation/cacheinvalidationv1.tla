----------------------------- MODULE cacheinvalidationv1 -----------------------------

EXTENDS Naturals

CONSTANTS
    KEYS


VARIABLES
    database,
    cache,
    cacheFillStates, \* cacheFillStatus[key] = Fill state
    invalidationQueue


INSTANCE cacherequirements

vars == <<database, cache, cacheFillStates, invalidationQueue>>

InvalidationMessage == [key: KEYS]

CacheFillState == [state: {"inactive", "started", "respondedto"}, version: DataVersion]

CacheValue == CacheMiss \union CacheHit

TypeOk ==
    /\ database \in [KEYS -> DataVersion]
    /\ cache \in [KEYS -> CacheValue]
    \* We track the cache fill state for each key. It is a multipart process
    /\ cacheFillStates \in [KEYS -> CacheFillState]
    \* We model invalidationQueue as a set, because we cannot guarantee in-order delivery
    /\ invalidationQueue \in SUBSET InvalidationMessage
    
Init ==
    /\ database = [k \in KEYS |-> 0]
    /\ cache = [k \in KEYS |-> [type |-> "miss"]]
    \* Cache fill states start inactive
    /\ cacheFillStates = [k \in KEYS |-> [
                                state |-> "inactive", 
                                \* Version set to earliest possible version
                                version |-> 0]
                          ]
    \* The invalidation queue starts empty
    /\ invalidationQueue = {}


DatabaseUpdate(k) ==
    \* The version of that key is incremented, representing a write
    /\ database' = [database EXCEPT
                        ![k] = database[k] + 1]
    \* Adds invalidation message to queue.
    \* We don't need to model a delay in adding message as the cache can 
    \* always delay handling message to similar effect.
    /\ invalidationQueue' = invalidationQueue \union {[key |-> k]}
    /\ UNCHANGED <<cache, cacheFillStates>>

\* Cache Fill behavior
CacheStartReadThroughFill(k) ==
    \* Read-through only occurs when the cache is unset for that value
    /\ cache[k] \in CacheMiss
    \* One cache fill request at a time
    /\ cacheFillStates[k].state = "inactive"
    /\ cacheFillStates' = [cacheFillStates EXCEPT ![k].state = "started"]
    /\ UNCHANGED <<database, cache, invalidationQueue>>

\* This is the moment the database provides a value for cache fill
DatabaseRespondToCacheFill(k) ==
    /\ cacheFillStates[k].state = "started"
    /\ cacheFillStates' = [cacheFillStates EXCEPT 
                            ![k].state = "respondedto",
                            ![k].version = database[k] 
                           ]
    /\ UNCHANGED <<database, cache, invalidationQueue>>
    
 \* Cache incorporates the data
CacheCompleteFill(k) == 
    /\ cacheFillStates[k].state = "respondedto"
    /\ cacheFillStates' = [cacheFillStates EXCEPT \* Reset to 0 
                            ![k].state = "inactive",
                            ![k].version = 0
                           ]
    /\ cache' = [cache EXCEPT
                        ![k] = [
                           \* Cache value is now a hit
                           type |-> "hit",
                           \* Set to whatever came back in response
                           version |-> cacheFillStates[k].version
                        ]
                ]
    /\ UNCHANGED <<database, invalidationQueue>>
    
\* Cache fails to fill
CacheFailFill(k) == 
    /\ cacheFillStates[k].state = "respondedto"
     \* Cache fill state is reset, having not filled cache
    /\ cacheFillStates' = [cacheFillStates EXCEPT
                            ![k].state = "inactive",
                            ![k].version = 0
                           ]
    /\ UNCHANGED <<database, cache, invalidationQueue>>
    
\* Handle invalidation message. Assume it is not taken off queue in case of
\* failure. Therefore failure modeled as CacheHandleInvalidationMessage not
\* occurring.
CacheHandleInvalidationMessage == 
    /\ \E message \in invalidationQueue: \* Dequeue invalidation queue in any order
        \* Remove message from queue
        /\ invalidationQueue' = invalidationQueue \ {message}
        \* Evict item from cache
        /\ cache' = [cache EXCEPT ![message.key] = [type |-> "miss"]]
    /\ UNCHANGED <<cacheFillStates, database>>

\* Cache eviction model is unchanged
CacheEvict(k) ==
    /\ cache[k] \in CacheHit
    /\ cache' = [cache EXCEPT ![k] = [type |-> "miss"]]
    /\ UNCHANGED <<database, cacheFillStates, invalidationQueue>>

\* The cache will always be able to...
CacheFairness ==
    \E k \in KEYS:
        \* Complete the cache fill process
        \/ CacheStartReadThroughFill(k) 
        \/ DatabaseRespondToCacheFill(k) \* Write
        \/ CacheCompleteFill(k)
        \* Process invalidation messages
        \/ CacheHandleInvalidationMessage



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
        \/ CacheHandleInvalidationMessage
        \/ CacheEvict(k)

\* Cache fairness is included as part of the specification of system behavior.
\* This is just how the system works.
Spec == Init /\ [][Next]_vars /\ WF_vars(CacheFairness)

=============================================================================
\* Modification History
\* Last modified Wed Jun 15 12:45:25 MST 2022 by elliotswart
\* Created Tue Jun 14 20:36:02 MST 2022 by elliotswart
