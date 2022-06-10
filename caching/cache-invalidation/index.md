---
layout: default
parent: Cache Invalidation
title: Adding cache invalidation
nav_order: 2
v1:
    2:
        note: Cache fill starts
    3:
        note: "Database responds with k1:v0"
    4:
        note: "Value changes to k1:v2, triggering invalidation"
    5:
        note: Key isn't in cache, does nothing
        class: text-red-300
    6:
        note: "Cache completes fill with old value. k1:v0"
        class: text-red-300
    stuttering:
        note: No more updates, and cache remains inconsistent
        show: true
v2:
    1: 
        note: A cache fill starts for k1
    4: 
        note: "An invalidation message is sent with k1:v1"
    5: 
        note: The invalidation message is ignored because k1 is not in cache
        class: text-red-300
    6: 
        note: "The outdated k1:v0 is loaded as fill comes back"
        class: text-red-300
    stuttering: 
        note: No more updates, and cache remains inconsistent
        show: true
---

{% include title_toc.md %}

## Designing an initial cache invalidation solution
As we determined earlier, we need to be able to systematically evict out-of-date values from the cache. We do that with cache invalidation.

Whenever the database updates a value, it put an invalidation message on a queue. The cache will process messages from that queue: if it contains the key it will evict the value, otherwise it will do nothing.

Assumptions:
- Our invalidation queue does not guarantee in-order delivery.
- Our invalidation queue is durable and guarantees at-least-once delivery.

### Initial cache invalidation
```plantuml
@startuml
participant "Writer" as Writer
participant "Database" as Database
participant "Cache Invalidation Queue" as Queue
participant "Cache" as Cache

Writer -> Database: Updates data
Database -> Queue: Adds updated key to queue
Queue <- Cache: Polls queue
Queue --> Cache: Returns invalidation item
Cache -> Cache: Evicts invalidated key from queue

alt Key not in Cache
    Cache -> Cache: Does nothing
end

@enduml
```

## Initial cache invalidation solution
### Modeling
We are now dealing with multiple processes, cache fill and invalidation, that may interact. Therefore it is necessary to break the processes down into their component steps, which may be executed simultaneously. Also, for context, a Cache Fill describes the process of the Cache requesting data from the **Database**, the **Database** responding, and the **Cache** incorporating that data.

It is now worthwhile to model the cache's state machine.

```plantuml
@startuml
hide empty description
[*] --> Inactive

Inactive --> CacheStartReadThroughFill
CacheStartReadThroughFill --> DatabaseRespondToCacheFill
DatabaseRespondToCacheFill --> CacheCompleteFill
DatabaseRespondToCacheFill --> CacheFailFill
@enduml
```

There is also a very simple message-handling state machine:
```plantuml
@startuml
hide empty description
[*] --> InvalidationMessageOnQueue
InvalidationMessageOnQueue --> CacheHandleInvalidationMessage
@enduml
```

Note that the cache requirements and the underlying data models that are checked stay the same.

{% include code.html path="cacheinvalidationv1" %}

### Verification
When we go to verify it we get an error:

{% include trace.html traceconfig=page.v1 constraint="Temporal property violated." trace=site.data.caching.cache-invalidation.v1 modelcfg="cacheinvalidation.cfg" %}

Clearly we have a race condition between cache invalidation and cache fill. Let's try to rectify that.

## Updated cache invalidation solution
### An updated design

So our data has been versioned all along for observability. It's time to start using the versions in our solution.  This isn't unrealistic, as databases can send snapshot times along with results and invalidations.

Let's also start sending the data along with the invalidations, so that we can update the cache when things change.

Whenever a cache fill comes back, or an invalidation message is received, we will compare the version we just received to the version in the cache. We will only modify the cache if the version is higher. That way we don't need to be concerned with race conditions of that sort. Whichever comes back first will be compared to the one that comes back second, and the cache will eventually have the same value.

#### Updated cache invalidation
```plantuml
@startuml
participant "Writer" as Writer
participant "Database" as Database
participant "Cache Invalidation Queue" as Queue
participant "Cache" as Cache

Writer -> Database: Updates data
Database -> Queue: Adds updated key and\nversioned data to queue
Queue <- Cache: Polls queue
Queue --> Cache: Returns invalidation item

alt Key not in Cache
    Cache -> Cache: Does nothing
end
alt Key in Cache
    Cache -> Cache: Does nothing
    
    alt Cache data older\nthan invalidation
        Cache -> Cache: Replaces old version\nwith data from message
    end
end

@enduml
```

### Modeling

We should update the state machines to:

```plantuml
@startuml
hide empty description
[*] --> Inactive

Inactive --> CacheStartReadThroughFill
CacheStartReadThroughFill --> DatabaseRespondToCacheFill
DatabaseRespondToCacheFill --> CacheCompleteFill
DatabaseRespondToCacheFill --> CacheFailFill
DatabaseRespondToCacheFill --> CacheIgnoreFill : fill version is older than stored version
@enduml
```

```plantuml
@startuml
hide empty description
[*] --> InvalidationMessageOnQueue
InvalidationMessageOnQueue --> CacheHandleInvalidationMessage
InvalidationMessageOnQueue --> CacheIgnoreInvalidationMessage : message version is older than stored version
@enduml
```

This is reflected in the code below.

{% include code.html path="cacheinvalidationv2" snippet="cacheinvalidationv2snippet" %}

### Verification
We run it and experience a different error.

{% include trace.html traceconfig=page.v2 constraint="Temporal property violated." trace=site.data.caching.cache-invalidation.v2 modelcfg="cacheinvalidation.cfg" %}

## Summary

Our main problem remaining is that cache invalidation messages are ignored if the key is not in the cache. In this case, a cache fill can be completed incorrectly with the old value. More broadly, the solution doesn't take ongoing cache fills into consideration. We should address this in our next design.

<br><br>

| Next: [Working cache invalidation](../working-cache-invalidation) |
