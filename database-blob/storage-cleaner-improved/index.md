---
layout: default
parent: Coordinating a Database and Blob Store
title: (Implementing New Requirements) Significant improvement
nav_order: 6
has_toc: false
trace:
    2: 
        note: Server s1 starts write at time 0
    3: 
        note: and successfully writes blob with id 1
    4: 
        note: Server s1 hangs at this point for 2 hours
        class: text-red-300
    6: 
        note: Server s2 starts to read a record for this user
    7: 
        note: The cleaner starts and gets the blob id 1 because 2 hours has passed
    8: 
        note: Blob id 1 is not in database, because write did not complete
    9: 
        note: Server s1 finishes writing
    10: 
        note: Server s2 reads the record under the assumption nothing is wrong
    11: 
        note: The cleaner deletes blob with id 1
        class: text-red-300
    12: 
        note: Server s2 reads an invalid blob
        class: text-red-300
kill:
    1:
        note: Let's see what's going on here
    5:
        note: A server successfully writes 
    7:
        note: 2 hours pass
    8:
        note: A server starts to update that same record
    10:
        note: A read is starting at the same time. No worries, we've handled this
    11:
        note: "Reads data that is about to change: image id is ui1"
    12:
        note: Write finishes, removing ui1 from the database
    13:
        note: The cleaner pounces and deletes ui1
    16:
        class: text-red-300
        note: The reader tries to read ui1 and fails

---
# {{page.title}}
{: .no_toc }

1. TOC
{:toc}

## Refining the design

How do we prevent the cleaner from deleting items just as they are being written? Well, the common sense solution is to check the creation time. We should only start cleaning a key after a safe window of time has passed since its creation. Let's call it 2 hours.

### Storage Cleaner Run
```plantuml
@startuml
participant "Storage Cleaner" as StorageCleaner
participant Database
participant "Blob Store" as BlobStore

StorageCleaner -> BlobStore: Gets batch of keys that have been created more than or exactly 2 hours ago
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

### Assumptions

We are making one main assumption: that all of our clocks are accurate within a reasonable margin of error (5 minutes is generous), and our code errs on the side of not deleting based on those margins.

While you can't always make assumptions about clock time in distributed systems, in this case our time frames are so large (hours) that it's probably not a bad assumption. Note: this doesn't mean a program will necessarily check its clock. It could stall and then resume what it's doing an hour later.

## Modeling the design
Now we have to introduce a concept of time in the model. You might think we've been using time throughout this whole tutorial, but actually, we were just using ordering. We will need to add the concept of creation time to the blob store. Keep in mind that the state diagram has not changed.

> _Note: This isn't adding functionality. We're just modeling details that have become relevant._

{% include code.html path="storagecleanerimproved" %}

## Verifying Storage Cleaner

We're going to start off with the slightly larger model (two servers and two cleaners), since the last test didn't show behavioral differences. Might as well perform the more rigorous test.

{% include trace.html traceconfig=page.trace constraint="Invariant ConsistentReads is violated." trace=site.data.database-blob.storage-cleaner-improved.trace modelcfg="storagecleanerimproved.cfg" namespace="trace" %}

The error we saw previously is gone, implying we fixed the design flaw we hoped to fix. This new error is much more complex. It requires the **Server** to stall at just the wrong time and be out of commission for 2 hours. This is pretty unlikely; in fact, it's unlikely enough that some companies might be okay with it. But the fix is obvious: kill the servers after 1 hour of stalling or less. Chances are we were going to do it anyway in implementation, but let's model it to get the extra assurance.

## A quick fix
All the changes in the model are in the server behavior. Despite the large number of changes, all we're really saying is that if less than an hour has passed since the server request started, it can proceed to the next state. Otherwise, it proceeds to the restart state.

This can be reflected in an updated state diagram for Server writes:

```plantuml
@startuml
hide empty description
[*] --> Waiting

Waiting --> StartWrite: Assigns start time
StartWrite --> WriteMetadata
StartWrite --> ServerRestart: timeout case
StartWrite --> FailWrite
WriteMetadata --> WriteBlobAndReturn
WriteMetadata --> ServerRestart: timeout case
WriteMetadata --> FailWrite
WriteBlobAndReturn --> Waiting
ServerRestart --> Waiting: timeout case
@enduml
```

This is reflected in the code below.

{% include code.html path="storagecleanerimprovedkillsnippet" %}

Looks good, right? Let's test it.

{% include trace.html traceconfig=page.kill constraint="Close but no cigar. Invariant ConsistentReads is violated." trace=site.data.database-blob.storage-cleaner-improved.kill namespace="kill" %}

We've gotten closer, and our error is even more obscure. Now it requires an interaction of **Storage Cleaner**, a **Read Server**, and a **Write Server**. But there's a relatively simple fix.

> _Note: This was the first error that I did not expect. But it is exciting that TLA+ wouldn't let me get away with it!_

<br><br>

| Next: [(Implementing New Requirements) A working update](../storage-cleaner-working) |