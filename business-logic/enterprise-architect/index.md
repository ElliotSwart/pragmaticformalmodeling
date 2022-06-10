---
layout: default
parent: Business Logic
title: Enterprise Architect gets us started
nav_order: 1

nonfunctionalRequirements:
    - text: The latency of all endpoints SHOULD be < 1 second
    - text: Data SHALL be encrypted at rest
    - text: Data SHALL be encrypted in transit

functionalRequirements:
    - text: The system SHALL have a **Start Subscription endpoint** 
      sub:
        - text: that is web accessible as an HTTP endpoint
    - text: When a request is received by the **Start Subscription endpoint** 
      sub:
        - text: if the requesting _User_ is _Subscribed_, the request SHALL return with 409 Conflict
        - text: if the requesting _User_ is _In Trial_, the trial SHALL end and the requesting _User_ SHALL be _Subscribed_
        - text: if the requesting _User_ is _Not Subscribed_ the requesting _User_ SHALL be _Subscribed_
        - text: if the requesting _User_ is scheduled to be _Not Subscribed_ due to cancellation the requesting _User_ SHALL remain _Subscribed_
    - text: The system SHALL have a **Cancel Subscription endpoint** 
      sub:
        - text: that is web accessible as an HTTP endpoint
    - text: When a request is received by the **Cancel Subscription endpoint** 
      sub:
        - text: if the requesting _User_ is not _Subscribed_, the request SHALL return with 409 Conflict
        - text: if the requesting _User_ is _Subscribed_ 
          sub:
            - text: the _User_ SHALL be _Not Subscribed_ at the end of the current month
            - text: if the user is _Not Subscribed_ at the end of the current month they SHALL be _Billed_ a _Cancellation Fee_
    - text: The system SHALL have a **Start Trial endpoint** 
      sub:
        - text: that is web accessible as an HTTP endpoint
    - text: When a request is received by the **Start Trial endpoint** 
      sub:
        - text: if the requesting _User_ is _Subscribed_, or _In Trial_ the request SHALL return with 409 Conflict
        - text: if the requesting _User_ has previously been _Subscribed_ or _In Trial_ the request SHALL return with 409 Conflict
        - text: "if the requesting _User_ is has never been _Subscribed_ or _In Trial_, that _User_ SHALL be _In Trial_. Justification: we only want new users to be able to start a trial"
    - text: The system SHALL have a **Cancel Trial Endpoint endpoint** 
      sub:
        - text: that is web accessible as an HTTP endpoint
    - text: When a request is received by the **Cancel Trial endpoint** 
      sub:
        - text: if the requesting _User_ is not _In Trial_ the request SHALL return with 409 Conflict
        - text: if the requesting _User_ is _In Trial_ the _User_ SHALL be _Not Subscribed_
    - text: The system SHALL have a **Watch Video endpoint** 
      sub:
        - text: that is web accessible as an HTTP endpoint
    - text: When a request is received by the **Watch Video endpoint** 
      sub:
        - text: if the requesting _User_ is not _In Trial_ or _Subscribed_ the request SHALL return with 409 Conflict
        - text: if the requesting _User_ is _In Trial_ or _Subscribed_ the system SHALL allow the _User_ to _Watch Video_
    - text: When a _User_ is _In Trial_ at the end of the month that the trial was started they SHALL be _Subscribed_
    - text: When a _User_ becomes _Subscribed_ 
      sub: 
        - text: they SHALL be _Billed_ the _Subscription Fee_ before the end of the month
        - text: if the requesting _User_ has _Post Due Payments_ they SHALL be _Billed_ in that amount before the end of the month, and _Post Due Payments_ SHALL be zeroed
    - text: When a _User_ is _Subscribed_ at the start of a month, they SHALL be _Billed_ the _Subscription Fee_
    - text: The system SHALL be able to interface with the **Payment Processor**
      sub:
        - text: it SHALL be able to call the **Bill endpoint** of the **Payment Processor**
        - text: it SHALL have a **Payment Failed endpoint**  that can accept the **Payment Processor** callback
    - text: When a _User_ is _Billed_ the system SHALL call the **Bill endpoint** of the **Payment Processor**
    - text: When a callback is received to the **Payment Failed endpoint** for a _User_ the system SHALL
      sub:
        - text: mark the _User_ as _Not Subscribed_
        - text: "set _Post Due Payments_ for the _User_ to: (failed payment amount) + _Failed Payment Fee_"

---

{% include title_toc.md %}

## Introduction
### Your bio

You're the kind of person who uses acronyms like [OLTP](https://en.wikipedia.org/wiki/Online_transaction_processing), [OLAP](https://en.wikipedia.org/wiki/Online_analytical_processing) and [OAuth](https://oauth.net/) in a sentence and knows what they mean. Whenever your company gets together for a game of Whiteboard, you win hands down. 
It's been a little while since you've coded anything, but it's like riding a bike: terrifying and dangerous. Modeling languages are fair game though! 

### Your assignment

1. Clarify the customers requirements into a requirements document
2. Distill the requirements document down into a formal specification
3. Come up with an architecture based on the requirements

By the end of this, coding the solution should be a piece of cake.

> Note: The client has only contracted us to build the backend software and expose APIs. A different firm is handling the frontend.

## Creating the requirements document

Through conversations with the customers, you have distilled their requirements into a standard format.

### Functional requirements

{% include requirements.md requirements=page.functionalRequirements %}

### Non-Functional requirements

{% include requirements.md requirements=page.nonfunctionalRequirements %}

## Requirements summary
You feel confident that you've gathered all the necessary requirements to ensure successful delivery on the contract. There are 44 requirements including sub-clauses, which is not that many, but you're worried some might be forgotten due to the tight deliverable schedule. Formal modeling seems like a good way to ensure that doesn't happen, but first you need to come up with an architecture.

## Architecture

Based on the requirements, it's safe to chose a simple architecture, with an autoscaling group of **Business Logic Servers** that access a **Database** hosted in a replica set. There is also an external **Payment Processor** that can accept bills, and occasionally provide _Payment Failed callbacks_.


```plantuml
@startuml
    skinparam fixCircleLabelOverlapping true 
    left to right direction

    
    component [Payment Processor] as PaymentProcessor
    database [Database]

    () "Database Connection" as DatabaseConnection

    
    component [Business Logic Servers] as Servers
    

    component [Clients]
    

    () "Payment Failed(user)" as PaymentFailed
    () "Bill(user, amount)" as Bill
    
    () "Start Subscription(user)" as StartSubscription
    () "Cancel Subscription(user)" as CancelSubscription
    () "Start Trial(user)" as StartTrial
    () "Cancel Trial(user)" as CancelTrial
    () "Watch Video(user)" as WatchVideo


    PaymentProcessor -up- Bill
    PaymentProcessor -up- PaymentFailed
    Clients --> WatchVideo
    Clients --> CancelTrial
    Clients --> StartTrial
    Clients --> CancelSubscription
    Clients --> StartSubscription

    Servers -down-> PaymentFailed
    Servers -down-> Bill

    Servers -up- WatchVideo
    Servers -up- CancelTrial
    Servers -up- StartTrial
    Servers -up- CancelSubscription
    Servers -up- StartSubscription
    
    [Database] -up- DatabaseConnection
    Servers ..> DatabaseConnection : uses
@enduml
```

Now that you've come up with the architecture, you're satisfied that it will work within the requirements and your team won't have any trouble with it.

## Creating the Formal Specification Model

Looking over the requirements, it's clear that only the Functional Requirements can be modeled. That might not always be true, but in this case they only influence implementation details and not the Business Logic itself. You don't want to provide the implementation details; after all, that's not your job. You need to write the spec in an implementation-agnostic way.

### The state machine

You create a state machine of the user workflow. The state machine here will not necessarily translate directly to a model, but it's still useful to have.

```plantuml
@startuml
hide empty description
[*] --> NotSubscribed
NotSubscribed --> SubscriptionStarted
NotSubscribed --> TrialStarted: Only if not subscribed or had trial
TrialStarted --> SubscriptionStarted
TrialStarted --> MonthElapsed
MonthElapsed --> SubscriptionStarted
TrialStarted --> TrialCanceled
TrialCanceled --> NotSubscribed
SubscriptionStarted --> SubscriptionCanceled
SubscriptionCanceled --> NotSubscribed
SubscriptionStarted --> PaymentFailed
PaymentFailed --> NotSubscribed
@enduml
```

### Data Model

The data model is shared between the specification and all the implementations. It lays out all the event types used for observability.
{% include code.html path="specdatamodels"%}

### Specification

You trace every requirement above to the specification. This is to ensure that every requirement is either represented formally or deliberately excluded.

{% include code.html path="speccannonical"%}

### Stubs
You write initial stubs for all the API calls such that you can add appropriate observability. You also provide the basic architecture of the spec to keep the assignment bounded.

{% include code.html path="stubs"%}

_Note: Generally you expect the first formal spec you write won't be perfect. If failures are being reported when they shouldn't, the spec may need to be revised. There's a collaborative process as the spec gets refined and becomes accurate. We've removed that from this narrative for simplicity. Assume there was a back-and-forth and you're seeing the 3rd revision of the spec above._

## Summary

Satisfied that you have specified and architected the system about as well as you can, you pass it off to a junior developer to implement. You work for a contracting firm. How else are you supposed to pay the bills?

<br><br>

| Next: [Junior Developer tries their best](../junior-dev) |