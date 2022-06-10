----------------------------- MODULE naivecache -----------------------------

EXTENDS Naturals

CONSTANTS
    KEYS \* The full set of keys in the database


VARIABLES
    database, \* database[key] = DataVersion
    cache \* cache[key] = CacheValue

\* Imports cache requirements to test against
INSTANCE cacherequirements


vars == <<database, cache>>

\* A cache can hold a hit or a miss for any given key
CacheValue == CacheMiss \union CacheHit

TypeOk ==
    \* database is a mapping of keys to a data version
    /\ database \in [KEYS -> DataVersion]
    \* cache is a mapping of kets to a cache value
    /\ cache \in [KEYS -> CacheValue]
    
Init ==
    \* All keys in the database are initialized to their first version
    /\ database = [k \in KEYS |-> 0]
    \* All keys in the cache are initialized to a miss, i.e. no data in cache
    /\ cache = [k \in KEYS |-> [type |-> "miss"]]


DatabaseUpdate(k) ==
    \* The version of that key is incremented, representing a write
    /\ database' = [database EXCEPT
                        ![k] = database[k] + 1]
    /\ UNCHANGED cache

CacheRead(k) == 
    \* The data is already in the cache
    /\ cache[k] \in CacheHit
    \* So the cache remains the same
    /\ UNCHANGED cache
    /\ UNCHANGED database

CacheReadThrough(k) ==
    \* The data is not in the cache
    /\ cache[k] \in CacheMiss 
    \* So it is read from the database
    /\ cache' = [cache EXCEPT
                        ![k] = [
                           \* Cache value is now a hit
                           type |-> "hit",
                           \* Set to whatever version is in database
                           version |-> database[k]
                        ]
                ]
    /\ UNCHANGED database
  
CacheEvict(k) ==
    \* The data is in cache, so can be evicted
    /\ cache[k] \in CacheHit
    \* cache[k]is turned into a miss
    /\ cache' = [cache EXCEPT ![k] = [type |-> "miss"]]
    /\ UNCHANGED database

(***************************************************************************)
(* Fairness: Normally no operation is guaranteed to happen; it just may.   *)
(* However, that means that the cache could just stop reading forever.     *)
(* And so it would never update. Now that doesn't seem reasonable.         *)
(***************************************************************************)

\* The cache will always be able to...
CacheFairness ==
    \E k \in KEYS:
        \/ CacheRead(k) \* Read
        \/ CacheReadThrough(k) \* Write
        \* CacheEvict(k) is not here, because CacheEvict is something that
        \*               may happen. It is not guaranteed



(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Next == 
    \E k \in KEYS:
        \* Database states
        \/ DatabaseUpdate(k)
        \* Cache states
        \/ CacheRead(k)
        \/ CacheReadThrough(k)
        \/ CacheEvict(k)

\* Cache fairness is included as part of the specification of system behavior.
\* This is just how the system works.
Spec == Init /\ [][Next]_vars /\ WF_vars(CacheFairness)

=============================================================================
\* Modification History
\* Last modified Tue Jun 14 22:51:06 MST 2022 by elliotswart
\* Created Tue Jun 14 20:36:02 MST 2022 by elliotswart
