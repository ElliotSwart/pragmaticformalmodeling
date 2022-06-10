---
layout: default
parent: Coordinating a Database and Blob Store
title: (Implementing New Requirements) A naive update
nav_order: 5
has_toc: false

single:
    3:
        note: Our server wrote an image
    4:
        note: Our cleaner starts
    5:
        note: and notices that the written image isn't in the database
    6:
        note: The server completes the write, thinking everything's fine
    7:
        note: A read starts for the same user
    9:
        note: But oh no, the cleaner deleted the key
    10:
        note: Leading to a corrupted read
        class: text-red-300

multi:
    10:
        note: Same corrupted read
        class: text-red-300
---
# {{page.title}}
{: .no_toc }

1. TOC
{:toc}

## Updating the design

The **Storage Cleaner** is going to to query the blob store and get a batch of keys. It will then query the database in one query and find all the images that are missing a database entry. Then it will delete those unused keys using a batch API call.
### Storage Cleaner Run
```plantuml
@startuml
participant "Storage Cleaner" as StorageCleaner
participant Database
participant "Blob Store" as BlobStore

StorageCleaner -> BlobStore: Gets batch of keys
StorageCleaner <-- BlobStore: Returns batch of keys

StorageCleaner -> Database : Queries for unused keys
StorageCleaner <-- Database: Returns unused keys

StorageCleaner -> BlobStore: Batch deletes unused keys
StorageCleaner <-- BlobStore: Returns status

alt any failure
    StorageCleaner --> StorageCleaner: Repeats from beginning
end

@enduml
```

## Modeling the design

This is the first example in our modeling tasks in which the model will not match the solution 1-1.
- **Relaxing a constraint**: While the design calls for batches, for simplicity's sake we will model it as if the entire blob store keyset can fit into one batch. This hides the complexity of figuring out which items have already been checked and how large of a batch size to use; we can either handle these considerations in implementation or model them separately. In this model, we will need to handle new keys being added after we query for keys, as well as the deletion process failing before all key are deleted. This should also alert us to problems that may be introduced by batching. _Note: This design decision is a judgment call that may or may not be correct, but it holds for the current examples._
- **Enhancing a constraint**: Deleting from the blob store will be modeled as a one by one operation, even though it is submitted in one API call. This is because blob stores don't provide transactions. A batch delete may happen over the course of time.

The **Storage Cleaner** state diagram looks like this:
```plantuml
@startuml
hide empty description
[*] --> Waiting

Waiting --> CleanerStartGetBlobKeys
CleanerStartGetBlobKeys --> CleanerGetUnusedKeys
CleanerStartGetBlobKeys --> CleanerFail
CleanerGetUnusedKeys --> CleanerDeletingKeys
CleanerGetUnusedKeys --> CleanerFail
CleanerDeletingKeys --> CleanerFinished
CleanerDeletingKeys --> CleanerFail
CleanerFinished --> Waiting

@enduml
```



Only the core additions to the spec are shown here. Click _Download Code_ or _Download PDF_ to see the whole thing.

{% include code.html path="storagecleanernaive" snippet="storagecleanernaive-snippet" %}

## Verifying the design

Let's start small and see what happens:

{% highlight tla %}
CONSTANTS
    SERVERS = {s1}
    CLEANERS = {c1}
{% endhighlight %}

{% include trace.html traceconfig=page.single constraint="Invariant ConsistentReads is violated." trace=site.data.database-blob.storage-cleaner-naive.single modelcfg="storagecleanernaive_small.cfg" %}

Let's try it again with two servers and two cleaners to see if we get different behavior.

{% highlight tla %}
CONSTANTS
    SERVERS = {s1, s2}
    CLEANERS = {c1, c2}
{% endhighlight %}

{% include trace.html traceconfig=page.multi constraint="Same behavior. Invariant ConsistentReads is violated." trace=site.data.database-blob.storage-cleaner-naive.multi modelcfg="storagecleanernaive.cfg" %}

Adding more servers and cleaners didn't change the failure mode. We've likely hit upon the essential failure of this design.

### Summary

Clearly this solution isn't going to work as is. It can delete images that were part of records being created at that moment. Normal cleanup systems don't do that; normally they wait a little while...

<br><br>

| Next: [(Implementing New Requirements) Significant improvement](../storage-cleaner-improved) |