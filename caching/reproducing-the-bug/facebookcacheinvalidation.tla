----------------------------- MODULE facebookcacheinvalidation -----------------------------

EXTENDS Naturals

CONSTANTS
    KEYS


VARIABLES
    database,
    \* Represents metadata version stored in the cache
    cache,
    \* Represents the version stored in the cache. This is what is used for comparisons,
    \* to allow our model to decouple ACTUAL metadata version with STORED version
    cacheVersions,
    cacheFillStates,
    invalidationQueue,
    counter

\* We can still test with the same cache requirements we've been using this whole time
INSTANCE cacherequirements

vars == <<database, cache, cacheFillStates, 
    invalidationQueue, counter, cacheVersions>>

InvalidationMessage == [key: KEYS, version: DataVersion]

CacheFillState == [
                    state: {
                        "inactive",
                         "startfillmetadata", 
                         "respondedtometadata", \* Next: CacheFillMetadata
                         "startfillversion", 
                         "respondedtoversion" \* Next: CacheFillVersion
                    },
                    version: DataVersion]

CacheValue == CacheMiss \union CacheHit

TypeOk ==
    /\ database \in [KEYS -> DataVersion]
    /\ cache \in [KEYS -> CacheValue]
    \* Cache versions are typed identically to cache
    /\ cacheVersions \in [KEYS -> CacheValue]
    /\ cacheFillStates \in [KEYS -> CacheFillState]
    /\ invalidationQueue \in SUBSET InvalidationMessage
    /\ counter \in Nat
    
Init ==
    /\ database = [k \in KEYS |-> 0]
    \* cache (metadata) and cacheVersions start empty together
    /\ cache = [k \in KEYS |-> [type |-> "miss"]]
    /\ cacheVersions = [k \in KEYS |-> [type |-> "miss"]]

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
    /\ invalidationQueue' = 
                invalidationQueue \union
                {[key |-> k, version |-> updatedVersion]}
    /\ UNCHANGED <<cache, cacheVersions, cacheFillStates, counter>>


CacheStartFillMetadata(k) ==
    \* Fill only occurs if the cache is unset for that value
    /\ cache[k] \in CacheMiss
    /\ cacheFillStates[k].state = "inactive"
    /\ cacheFillStates' = [cacheFillStates EXCEPT ![k].state = "startfillmetadata"]
    /\ UNCHANGED <<database, cache, cacheVersions,
                         invalidationQueue, counter>>

DatabaseRespondWithMetadata(k) ==
    /\ cacheFillStates[k].state = "startfillmetadata"
    /\ cacheFillStates' = [cacheFillStates EXCEPT 
                            ![k].state = "respondedtometadata",
                            ![k].version = database[k] 
                           ]
    /\ UNCHANGED <<database, cache, cacheVersions,
                         invalidationQueue, counter>>


\* Metadata updated in cache
CacheFillMetadata(k) == 
    /\ cacheFillStates[k].state = "respondedtometadata"
    /\ cacheFillStates' = [cacheFillStates EXCEPT
                            ![k].state = "inactive"
                           ]
    \* Represents cache metadata being updated
    \* Does not check version
    /\ cache' = [cache EXCEPT
                        ![k] = [
                           type |-> "hit",
                           version |-> cacheFillStates[k].version
                        ]
                ]
    /\ UNCHANGED <<database, cacheVersions, invalidationQueue, counter>>


CacheStartFillVersion(k) ==
    \* Fill only occurs if the cacheVersion is unset for that value
    /\ cacheVersions[k] \in CacheMiss
    /\ cacheFillStates[k].state = "inactive"
    /\ cacheFillStates' = [cacheFillStates EXCEPT ![k].state = "startfillversion"]
    /\ UNCHANGED <<database, cache, cacheVersions,
                         invalidationQueue, counter>>

DatabaseRespondWithVersion(k) ==
    /\ cacheFillStates[k].state = "startfillversion"
    /\ cacheFillStates' = [cacheFillStates EXCEPT 
                            ![k].state = "respondedtoversion",
                            ![k].version = database[k] 
                           ]
    /\ UNCHANGED <<database, cache, cacheVersions,
                         invalidationQueue, counter>>


\* Version updated in cache
CacheFillVersion(k) == 
    /\ cacheFillStates[k].state = "respondedtoversion"
    \* Fill empty versions
    /\  \/ cacheVersions[k] \in CacheMiss
        \* or newer versions
        \/ /\ cacheVersions[k] \in CacheHit
           /\ cacheVersions[k].version < cacheFillStates[k].version
           
    /\ cacheFillStates' = [cacheFillStates EXCEPT
                            ![k].state = "inactive"
                           ]
    \* Represents cache versions being updated
    /\ cacheVersions' = [cacheVersions EXCEPT
                            ![k] = [
                               type |-> "hit",
                               version |-> cacheFillStates[k].version
                            ]
                         ]
    /\ UNCHANGED <<database, invalidationQueue, cache, counter>>

CacheIgnoreFillVersion(k) == 
    /\ cacheFillStates[k].state = "respondedtoversion"
    \* If we have a newer version in cache, ignore fill
    /\ /\ cacheVersions[k] \in CacheHit
       /\ cacheVersions[k].version >= cacheFillStates[k].version
    /\ cacheFillStates' = [cacheFillStates EXCEPT \* Reset to 0 
                            ![k].state = "inactive",
                            ![k].version = 0
                           ]
    /\ counter' = counter + 1
    /\ UNCHANGED <<cache, cacheVersions,
                        database, invalidationQueue>>


CacheFailFill(k) ==
    /\ cacheFillStates[k].state \in {"respondedtometadata", "respondedtoversion"}
   
    /\ cacheFillStates' = [cacheFillStates EXCEPT
                            ![k].state = "inactive",
                            ![k].version = 0
                           ]
    /\ counter' = counter + 1           
    /\ UNCHANGED <<database, cache, cacheVersions,
                         invalidationQueue>>
                         
CacheEvict(k) ==
    /\ cache[k] \in CacheHit
    /\ cacheFillStates[k].state = "inactive"
    /\ cache' = [cache EXCEPT ![k] = [type |-> "miss"]]
    /\ cacheVersions' = [cache EXCEPT ![k] = [type |-> "miss"]]
    /\ counter' = counter + 1
    /\ UNCHANGED <<database, cacheFillStates, 
                    invalidationQueue>>

(***************************************************************************)
(* Invalidation message handling                                           *)
(***************************************************************************)

UpdateFromInvalidationMessage ==
    \E message \in invalidationQueue:
           \* Can update with no version
        /\ \/ /\ cache[message.key] \in CacheHit
              /\ cacheVersions[message.key] \in CacheMiss
           \* or with greater or equal version
           \/ /\ cacheVersions[message.key] \in CacheHit
              /\ cacheVersions[message.key].version <= message.version
    
        \* Kills pending fill request
        /\ cacheFillStates[message.key].state = "inactive"
        
        (***********************************************************************)
        (* Unlike fills from the database, the invalidation message contains   *)
        (* both version and metadata.                                          *)
        (***********************************************************************)
        /\ cache' = [cache EXCEPT 
                        ![message.key] = [
                            type |-> "hit",
                            version |-> message.version
                        ]]
        /\ cacheVersions' = [cache EXCEPT 
                ![message.key] = [
                    type |-> "hit",
                    version |-> message.version
                ]]
        /\ invalidationQueue' = invalidationQueue \ {message}
        /\ UNCHANGED <<cacheFillStates, database, counter>>


FailUpdateInvalidationMessageEvictKey ==
    \E message \in invalidationQueue:
           \* Can update with no version
        /\ \/ /\ cache[message.key] \in CacheHit
              /\ cacheVersions[message.key] \in CacheMiss
           \* or with greater version
           \/ /\ cacheVersions[message.key] \in CacheHit
              /\ cacheVersions[message.key].version < message.version
        \* Kills pending fill request
        /\ cacheFillStates[message.key].state = "inactive"
        \* Key is evicted from cache, to allow fresh cache fill
        /\ cache' = 
                [cache EXCEPT 
                        ![message.key] = [type |-> "miss"]]
        /\ cacheVersions' = 
                [cacheVersions EXCEPT 
                        ![message.key] = [type |-> "miss"]]
                        
        /\ invalidationQueue' = invalidationQueue \ {message}
        /\ UNCHANGED <<cacheFillStates, database, counter>>
        
FailUpdateInvalidationMessageIgnore ==
    \E message \in invalidationQueue:
       \* If message version is lower or equal than cache version, do nothing
        /\ cacheVersions[message.key] \in CacheHit
        /\ cacheVersions[message.key].version >= message.version
        /\ counter' = counter + 1
        /\ invalidationQueue' = invalidationQueue \ {message}
        /\ UNCHANGED <<cacheFillStates, database, 
                                cache, cacheVersions>>

IgnoreInvalidationMessage == 
    \E message \in invalidationQueue:
        \* Ignore invalidation messages if a key is not in cache
        /\ \/ /\ cache[message.key] \in CacheMiss
              \* and a fill is not occurring
              /\ cacheFillStates[message.key].state = "inactive"
           \* or when the cache already has a larger version
           \/ /\ cacheVersions[message.key] \in CacheHit
              /\ cacheVersions[message.key].version > message.version
        /\ invalidationQueue' = invalidationQueue \ {message}
        /\ counter' = counter + 1
        \* Don't update cache
        /\ UNCHANGED <<cacheFillStates, database, cache, cacheVersions>>
    

CacheFairness ==
    \/ \E k \in KEYS:
        \/ CacheStartFillMetadata(k) 
        \/ DatabaseRespondWithMetadata(k)
        \/ CacheFillMetadata(k)
        \/ CacheStartFillVersion(k) 
        \/ DatabaseRespondWithVersion(k)
        \/ CacheFillVersion(k)
        \/ CacheIgnoreFillVersion(k)
    \/ UpdateFromInvalidationMessage
    \/ FailUpdateInvalidationMessageEvictKey
    \/ FailUpdateInvalidationMessageIgnore
    \/ IgnoreInvalidationMessage
    
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Next == 
    \/ \E k \in KEYS:
        \* Database states
        \/ DatabaseUpdate(k)
        \* Cache states
        \/ CacheStartFillMetadata(k) 
        \/ DatabaseRespondWithMetadata(k)
        \/ CacheFillMetadata(k)
        \/ CacheStartFillVersion(k) 
        \/ DatabaseRespondWithVersion(k)
        \/ CacheFillVersion(k)
        \/ CacheIgnoreFillVersion(k)
        \/ CacheEvict(k)
        \/ CacheFailFill(k)
    \/ UpdateFromInvalidationMessage
    \/ FailUpdateInvalidationMessageEvictKey
    \/ FailUpdateInvalidationMessageIgnore
    \/ IgnoreInvalidationMessage

Spec == Init /\ [][Next]_vars /\ WF_vars(CacheFairness)


CounterBound == counter =< 2


=============================================================================
\* Modification History
\* Last modified Thu Jun 16 16:19:54 MST 2022 by elliotswart
\* Created Tue Jun 14 20:36:02 MST 2022 by elliotswart
