-------------------------------- MODULE specprincipal --------------------------------
(***************************************************************************)
(* A single page version for easier testing                                *)
(***************************************************************************)


EXTENDS Sequences, Naturals, FiniteSets

(***************************************************************************)
(* specdatamodels.tla                                                      *)
(***************************************************************************)

(***************************************************************************)
(* An ordered event stream of every event that occurs in the system.       *)
(* All the specifications will be written based on it.                     *)
(* This is an observability value that you wouldn't have access to in the  *)
(* implementation. We'll only have the API method stubs write to it; no    *)
(* implementation may read from it. This will be enforced with code review *)
(***************************************************************************)
VARIABLE events

\* Represents every potential user in the system
CONSTANT USERS

\* Constants that should be set to single model values to allow comparisons.
\* Only equality comparisons will be made.
CONSTANTS
    SubscriptionFee,
    CancellationFee,
    FailedPaymentFee

Fees == {SubscriptionFee, CancellationFee, FailedPaymentFee}

(***************************************************************************)
(* Event Types: Describes everything that can happen in the system         *)
(***************************************************************************)

MonthPassEvent == [type : {"monthpass"}]

StartSubscriptionEvent == [type : {"startsubscription"}, user: USERS]
CancelSubscriptionEvent == [type : {"cancelsubscription"}, user: USERS]

StartTrialEvent == [type : {"starttrial"}, user: USERS]
CancelTrialEvent == [type : {"canceltrial"}, user: USERS]

WatchVideoEvent == [type : {"watchvideo"}, user: USERS]

BillEvent == [type : {"bill"}, user: USERS, fee: Fees]
PaymentFailedEvent == [type : {"paymentfailed"}, user: USERS, fee: Fees]

Event ==
    MonthPassEvent \union
    StartSubscriptionEvent \union
    CancelSubscriptionEvent \union
    StartTrialEvent \union
    CancelTrialEvent \union
    WatchVideoEvent \union
    BillEvent \union
    PaymentFailedEvent

EventsOk ==
    events \in Seq(Event)
    
VARIABLES
    month,
    database

vars == <<events, month, database>>

Now == Len(events)

Months == 0..10

(***************************************************************************)
(* Strong Typing                                                           *)
(***************************************************************************)

Month == Nat

(***************************************************************************)
(* Database Rows                                                           *)
(***************************************************************************)
VideoAccessRow == 
    [type : {"enabled", "disabled"}] \union
    [
        type : {"disabledasoftimestamp"},
        disabledtime: Month
    ]

TrialStatusRow == 
    [type: {"eligible", "ineligible", "cancelled"}] \union
    [
        type : {"started"},
        endtime: Month
    ]

SubscriptionStatusRow == 
    [ type: {"notsubscribed", "subscribed", "tocancel"}] \union
    [
        type: {"tocancel"},
        canceltime: Month
    ]

UpcomingChargeItem == [fee : Fees, event: Nat]


TypeOk ==
    /\ EventsOk
    /\ month \in Month
    \* Represents a singleton record type tracking the billing month
    /\ database.billingMonth \in Month
    \* Table with VideoAccessRow definition
    /\ database.videoAccess \in [USERS -> VideoAccessRow]
    \* Table with TrialStatusRow definition
    /\ database.trial \in [USERS -> TrialStatusRow]
    \* Table with SubscriptionStatusRow definition
    /\ database.subscription \in [USERS -> SubscriptionStatusRow]
    \* A row index, by user and month, that holds UpcomingCharges
    /\ database.upcomingCharges \in [USERS -> [Months -> SUBSET UpcomingChargeItem]]
    \* Table with PastDueStatus row definition
    /\ database.inGoodStanding \in [USERS -> BOOLEAN]

    
(***************************************************************************)
(* API endpoints                                                           *)
(***************************************************************************)

\* Database query:
IsSubscribed(u) == 
    \/ database.subscription[u].type = "subscribed"
    \* A converted trial that hasn't been processed in database
    \/ /\ database.trial[u].type = "started"
       /\ database.trial[u].endtime <= month

StartSubscription(u) ==
    LET paymentFailedCharges == 
        IF database.inGoodStanding[u] = TRUE
        THEN {}
        ELSE {[event |-> Now, fee |-> FailedPaymentFee]}
    IN

    
    LET thisMonthsCharges == 
        database.upcomingCharges[u][month] \union
        \* Add payment failed fee if applicable
        paymentFailedCharges
    IN

    \* Remove cancellation fee for next month
    LET nextMonthsCharges == {
            c \in database.upcomingCharges[u][month+1]: 
                    c.fee # CancellationFee
    }
    IN
    \* Transaction precondition
    /\ ~IsSubscribed(u)
    \* Transaction
    /\ database' = 
        [database EXCEPT
            !["inGoodStanding"][u] = TRUE,
            !["subscription"][u] =  [type |-> "subscribed"],
            !["trial"][u] = [type |-> "ineligible"],
            !["videoAccess"][u] = [type |-> "enabled"],
            \* Add charges
            !["upcomingCharges"][u][month] = thisMonthsCharges,
            !["upcomingCharges"][u][month+1] = nextMonthsCharges
        ]
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "startsubscription", user |-> u])
    /\ UNCHANGED month


CancelSubscription(u) ==
    LET cancelTime == month + 1 IN
    LET cancellationFee == [
                            event |-> Now, 
                            fee |-> CancellationFee] 
    IN
    LET subscriptionFee == 
        [event |-> Now, 
         fee |-> SubscriptionFee]
    IN
    \* Adds subscription fee for this month if not already added
    LET thisMonthsCharges == IF ~\E charge \in database.upcomingCharges[u][month]:
                                    charge.fee = SubscriptionFee
                             THEN database.upcomingCharges[u][month] \union
                                  {subscriptionFee}
                             ELSE database.upcomingCharges[u][month]
    IN
    \* Transaction precondition
    /\ IsSubscribed(u)
    \* Transaction
    /\ database' = 
        [database EXCEPT
            !["trial"][u] = [type |-> "ineligible"],
            !["subscription"][u] =  [type |-> "tocancel", canceltime |-> cancelTime],
            !["videoAccess"][u] = [type |-> "disabledasoftimestamp", 
                                   disabledtime |-> cancelTime],
            !["upcomingCharges"][u][month] = thisMonthsCharges,
            \* Queue up cancellation fee for next month
            !["upcomingCharges"][u][month + 1] = 
                database.upcomingCharges[u][month] \union 
                {cancellationFee}
        ]
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "cancelsubscription", user |-> u])
    /\ UNCHANGED <<month>>

    
StartTrial(u) ==
    LET endTime == month + 1 IN

 
    \* Transaction precondition
    /\ database.trial[u].type = "eligible"
    \* Transaction
    /\ database' = 
        [database EXCEPT
            !["trial"][u] = [type |-> "started", 
                             endtime |-> endTime],
            !["videoAccess"][u] = 
                            [type |-> "enabled"]
        ]
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "starttrial", user |-> u])
    /\ UNCHANGED <<month>>
    

CancelTrial(u) ==
    \* Transaction precondition
    /\ database.trial[u].type = "started"
    \* The trial has not already ended
    /\ database.trial[u].endtime > month
    \* Transaction
    /\ database' = 
        [database EXCEPT
            !["trial"][u] = [type |-> "cancelled"],
            !["videoAccess"][u] = 
                            [type |-> "disabled"]
        ]
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "canceltrial", user |-> u])
    /\ UNCHANGED <<month>>

\* Database query
WatchVideoAuthorized(u) == 
    \/ database.videoAccess[u].type = "enabled"
    \/ /\ database.videoAccess[u].type = "disabledasoftimestamp"
       /\ database.videoAccess[u].disabledtime > month

WatchVideo(u) ==
    /\ WatchVideoAuthorized(u)
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "watchvideo", user |-> u])
    /\ UNCHANGED <<month, database>>


Bill(u, fee) ==
    /\ events' = Append(events, [type |-> "bill", 
                                 user |-> u, 
                                 fee |-> fee])

PaymentFailed(u, fee) ==
    /\ database' = 
        [database EXCEPT
            !["inGoodStanding"][u] = FALSE,
            !["subscription"][u] =  [type |-> "notsubscribed"],
            !["trial"][u] = [type |-> "ineligible"],
            !["videoAccess"][u] = [type |-> "disabled"],
            \* Remove all upcoming changes
            !["upcomingCharges"][u][month] = {},
            !["upcomingCharges"][u][month+1] = {}
        ]
    /\ events' = Append(events, [type |-> "paymentfailed", 
                                 user |-> u , 
                                 fee |-> fee])
    /\ UNCHANGED <<month>>

(***************************************************************************)
(* Recurring Operations                                                    *)
(***************************************************************************)

\* This the the state that calls the Payment Failed API
ExistingBillFailed == 
    \/ \E i \in 1..Len(events):
        \* Only a past bill can fail
        /\ events[i] \in BillEvent
        /\ PaymentFailed(events[i].user, events[i].fee)

\* Trial users that have passed trial period are subscribed
ConvertTrialUser(u) ==
    /\ database.trial[u].type = "started"
    /\ database.trial[u].endtime <= month \* The trial has ended
    \* Transaction
    /\ database' = 
        [database EXCEPT
            !["subscription"][u] =  [type |-> "subscribed"],
            !["trial"][u] = [type |-> "ineligible"],
            !["videoAccess"][u] = [type |-> "enabled"]
        ]
    /\ UNCHANGED <<month, events>>

\* Cancelled users that have passed cancellation period are unsubscribed
ProcessCancelledUser(u) ==
    /\ database.subscription[u].type = "tocancel"
    /\ database.subscription[u].canceltime <= month
    /\ database' = [database EXCEPT
            \* unsubscribe
            !["subscription"][u] =  [type |-> "notsubscribed"]
        ]
    /\ UNCHANGED <<month, events>>

\* Any subscribed user is billed this month
BillUserForSubscription(u) ==
    LET subscriptionFee == 
        [event |-> Now, 
         fee |-> SubscriptionFee]
    IN
    /\ database.subscription[u].type = "subscribed"
    \* Add subscription fee for this month
    /\ database' = 
        [database EXCEPT
                !["upcomingCharges"][u][month] = 
                    database.upcomingCharges[u][month] \union 
                    {subscriptionFee}
        ]
    /\ UNCHANGED <<month, events>>

\* Bill users for their current month charges
ProcessCharges ==
    /\ \E u \in USERS:
        LET monthlyCharges == database.upcomingCharges[u][month] IN
        \* If there are upcoming charges for this month
        /\ Cardinality(monthlyCharges) > 0
        \* Dequeue a bill
        /\ \E charge \in monthlyCharges:
            \* Submit to payment processor
            /\ Bill(u, charge.fee)
            \* Delete from queue
            /\ database' = 
                [database EXCEPT
                    !["upcomingCharges"][u][month] = monthlyCharges \ {charge}
                ]
    /\ UNCHANGED month

(***************************************************************************)
(* Stub method that prevents the month from passing until all operations   *)
(* are complete. Represent worker methods, etc.                            *)
(***************************************************************************)
HandledMonth ==
    /\ ~ENABLED ProcessCharges
    /\ \A u \in USERS:
        /\ ~ENABLED ConvertTrialUser(u)
        /\ ~ENABLED ProcessCancelledUser(u)
        /\ ~ENABLED BillUserForSubscription(u)


\* DO NOT MODIFY
MonthPasses ==
    /\ HandledMonth
    /\ month' = month + 1
    /\ events' = Append(events, [type |-> "monthpass"])
    /\ UNCHANGED <<database>>

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Init ==
    /\ events = <<>> \* Events must be intialized empty, per stub
    /\ month = 0
    /\ database = [
            \* No months have been billed for yet
            billingMonth |-> 0,
            \* No user starts with access
            videoAccess |-> [u \in USERS |-> [type |-> "disabled"]],
            \* Every user starts eligible for trial
            trial |-> [u \in USERS |-> [type |-> "eligible"]],
            \* Every user starts not subscribed
            subscription |-> [u \in USERS |-> [type |-> "notsubscribed"]],
            \* All users start in good standing
            inGoodStanding |-> [u \in USERS |-> TRUE],
            \* No bills to submit
            upcomingCharges |-> [u \in USERS |-> [x \in Months |-> {}]]
        ]

Next ==
    \* Required by stub
    \/ MonthPasses
    \* State modified below
    \/ \E u \in USERS:
            \/ StartSubscription(u)
            \/ CancelSubscription(u)
            \/ StartTrial(u)
            \/ CancelTrial(u)
            \/ WatchVideo(u)
            \/ ConvertTrialUser(u)
            \/ ProcessCancelledUser(u)
            \/ ConvertTrialUser(u)
            \/ BillUserForSubscription(u)
    \* Payment failing behavior is part of spec, not implementation
    \/ ExistingBillFailed
    \/ ProcessCharges

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* spec.tla                                                                *)
(***************************************************************************)

(***************************************************************************)
(* Trace requirements to specification                                     *)
(*                                                                         *)
(*  Not Traceable                                                          *)  
(*      Functional: 1,2,3,6,7,9,14                                         *)
(*      NonFunctional: 1,2,3                                               *)
(***************************************************************************)

(***************************************************************************)
(* Definitions                                                             *)
(***************************************************************************)

InTrial(u, end) ==
    \E i \in 1..end:
        /\ events[i] \in StartTrialEvent \* Has started trial
        /\ events[i].user = u
        (*******************************************************************)
        (* 6. Start Trial endpoint request                                 *)
        (* 6.3 If the requesting User has never been Subscribed or In      *)
        (*     Trial, that User SHALL be In Trial                          *)
        (*******************************************************************)
        /\ ~\E j \in i..end: \* And not canceled
            /\ events[j] \in
                (************************************************************)
                (* 8 Cancel Trial endpoint request                          *)
                (* 8.2 [Partial] If the requesting User is In Trial, the    *)
                (*      User SHALL be Not Subscribed                        *)
                (************************************************************)
                CancelTrialEvent \union
                (************************************************************)
                (* 2. Start Subscription endpoint request                   *)
                (* 2.2 If the requesting User is In Trial, the trial SHALL  *)
                (*     end and the requesting User SHALL be Subscribed      *)
                (************************************************************)
                StartSubscriptionEvent
            /\ events[j].user = u

                
        (*******************************************************************)
        (* 11 [Partial] When a User is In Trial at the end of the month    *)
        (*    that the trial was started, they SHALL be Subscribed         *)
        (*******************************************************************)
        /\ ~\E j \in i..end:
            /\ events[j] \in MonthPassEvent



UnsubscribedAfterEvent(u, i, end) ==
    \E j \in i..end: \* And not unsubscribed after
        /\ events[j] \notin MonthPassEvent
        /\ events[j].user = u
        (************************************************************)
        (* Cancel Subscription endpoint request                     *)
        (* 4.2.1 User SHALL be Not Subscribed at the end of the     *)
        (*       current month                                      *)
        (************************************************************)
        /\ \/ /\ events[j] \in CancelSubscriptionEvent
              /\ \E k \in j..end: events[k] \in MonthPassEvent
           (************************************************************)
           (* 16. User has payment failed                              *)
           (* 16.1 mark the User as Not Subscribed                     *)
           (************************************************************)
           \/ events[j] \in PaymentFailedEvent



SubscribedFromStartSubscription(u, end) ==
    (*******************************************************************)
    (* 2.4 If the requesting User is scheduled to be Not Subscribed    *)
    (*     due to cancellation, the requesting User SHALL remain       *)
    (*     Subscribed                                                  *)
    (* Implemented because a StartSubscriptionEvent after Cancel       *)
    (* undoes the cancel.                                              *)
    (*******************************************************************)
    \E i \in 1..end:
        /\ events[i] \in StartSubscriptionEvent \* Has subscribed
        /\ events[i].user = u
        /\ ~UnsubscribedAfterEvent(u, i, end)

AboutToCancel(u, end) ==
    \E i \in 1..end:
        /\ events[i] \in CancelSubscriptionEvent
        /\ ~\E j \in i..end:
            events[j] \in MonthPassEvent \union
                          StartSubscriptionEvent

SubscribedFromTrial(u, end) ==
    (*******************************************************************)
    (* 11 [Partial] When a User is In Trial at the end of the month    *)
    (*    that the trial was started, they SHALL be Subscribed         *)
    (*******************************************************************)
    \E i \in 1..end:
        /\ events[i] \in StartTrialEvent \* Has started trial
        /\ events[i].user = u
        /\ ~InTrial(u, end) \* Requirement fulfilled through InTrial
        /\ ~UnsubscribedAfterEvent(u, i, end)
        (************************************************************)
        (* Cancel Trial endpoint request                            *)
        (* 8.2 [Partial] If the requesting User is In Trial, the    *)
        (*     User SHALL be Not Subscribed                         *)
        (************************************************************)
        /\ ~\E j \in i..end: \* And not canceled
            /\ events[j] \in CancelTrialEvent
            /\ events[j].user = u
            


                
Subscribed(u, end) == 
    \/ SubscribedFromStartSubscription(u, end)
    \/ SubscribedFromTrial(u, end)




(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)


(***************************************************************************)
(* 2 When a request is received by the Start Subscription endpoint         *)
(***************************************************************************)
StartSubscriptionAccessControl ==
    \A u \in USERS:
        LET authorized == ~Subscribed(u, Now) \/ AboutToCancel(u, Now) IN
        (*******************************************************************)
        (* 2.1: If the requesting User is Subscribed, the request SHALL    *)  
        (*      return with 409 Conflict                                   *)
        (*******************************************************************)
        \/ /\ ~authorized
           /\ ~ENABLED StartSubscription(u)

        (*******************************************************************)
        (* 2.2 [Partial]: If the requesting User is In Trial, the trial    *)
        (*      SHALL end and the requesting User SHALL be Subscribed      *)
        (*******************************************************************)
        (*******************************************************************)
        (* 2.3: If the requesting User is Not Subscribed, the requesting   *)
        (*        User SHALL be Subscribed                                 *)
        (*******************************************************************)
        \/ /\ authorized
           /\ ENABLED StartSubscription(u)

(***************************************************************************)
(* 4 When a request is received by the Cancel Subscription endpoint        *)
(***************************************************************************)
CancelSubscriptionAccessControl ==
    \A u \in USERS:
        LET authorized == Subscribed(u, Now) /\ ~AboutToCancel(u, Now) IN
        (*******************************************************************)
        (* 4.1 If the requesting User is not Subscribed, the request SHALL *)
        (*     return with 409 Conflict                                    *)
        (*******************************************************************)
        \/ /\ ~authorized
           /\ ~ENABLED CancelSubscription(u)
        (*******************************************************************)
        (* 4.2 [Partial]: If the requesting User is Subscribed, the User   *)  
        (*      SHALL ... [Cancellation Requirements]                      *)
        (*******************************************************************)
        \/ /\ authorized
           /\ ENABLED CancelSubscription(u)


(***************************************************************************)
(* 6.3 [Partial] If the requesting User is has never been Subscribed,      *)
(*      or is In Trial                                                     *)
(***************************************************************************)
EligibleForTrial(u) ==
    ~\E i \in 1..Len(events):
        /\ events[i] \in
            StartSubscriptionEvent \union
            StartTrialEvent
        /\ events[i].user = u

(***************************************************************************)
(* 6 When a request is received by the Start Trial endpoint                *)
(***************************************************************************)
StartTrialAccessControl ==
    \A u \in USERS:
        (*******************************************************************)
        (* 6.1 If the requesting User is Subscribed or In Trial, the       *)
        (*     request SHALL return with 409 Conflict                      *)
        (*******************************************************************)
        (*******************************************************************)
        (* 6.2 If the requesting User has previously been Subscribed or    *)
        (*     In Trial, the request SHALL return with 409 Conflict        *)
        (*******************************************************************)   
        \/ /\ ~EligibleForTrial(u)
           /\ ~ENABLED StartTrial(u)
        (*******************************************************************)
        (* 6.3 If the requesting User has never been Subscribed or         *)
        (*     In Trial, that User SHALL be In Trial                       *)
        (*******************************************************************) 
        \/ /\ EligibleForTrial(u)
           /\ ENABLED StartTrial(u)


(***************************************************************************)
(* 8 When a request is received by the Cancel Trial endpoint               *)
(***************************************************************************)
CancelTrialAccessControl == 
    \A u \in USERS:
                 
        (*******************************************************************)
        (* 8.1 If the requesting User is not In Trial, the request SHALL   *)
        (*     return with 409 Conflict                                    *)
        (*******************************************************************) 
        \/ /\ ~InTrial(u, Now)
           /\ ~ENABLED CancelTrial(u)
                       
        (*******************************************************************)
        (* 8.2 [Partial] If the requesting User is In Trial, the User      *)
        (*     SHALL be Not Subscribed                                     *)
        (*******************************************************************) 
        \/ /\ InTrial(u, Now)
           /\ ENABLED CancelTrial(u)

(***************************************************************************)
(* 10 When a request is received by the Watch Video endpoint               *)
(***************************************************************************)
WatchVideoAccessControl ==
    \A u \in USERS:
        (*******************************************************************)
        (* 10.1 If the requesting User is not In Trial or Subscribed, the  *)
        (*      request SHALL return with 409 Conflict                     *)
        (*******************************************************************)
        \/ /\ ~InTrial(u, Now) /\ ~Subscribed(u, Now)
           /\ ~ENABLED WatchVideo(u)
        (*******************************************************************)
        (* 10.2 If the requesting User is In Trial or Subscribed, the      *) 
        (*      system SHALL allow the User to Watch Video                 *)
        (*******************************************************************)
        \/ /\ InTrial(u, Now) \/ Subscribed(u, Now)
           /\ ENABLED WatchVideo(u)

(***************************************************************************)
(* Runs a given operation between: 1 - first month for the first month,    *) 
(* and month i - month i + 1                                               *)
(***************************************************************************)
TrueForEveryUserMonth(op(_,_,_), checkFirstMonth) ==
    LET numMonthPass == Cardinality({i \in 1..Len(events): events[i]
                                                 \in MonthPassEvent}) 
    IN
    \* If checking the first month
    /\ \/ ~checkFirstMonth
       \/ /\ checkFirstMonth
        \* There does not exist 
          /\ ~\E i \in 1..Len(events):
            \* a first month
            /\ events[i] \in MonthPassEvent
            /\ ~\E j \in 1..i: events[j] \in MonthPassEvent
            \* Where the op is false for any user
            /\ \E u \in USERS: 
                ~op(u,1,i)

    \* There does not exist a pair of consecutive months
    /\ ~\E i \in 1..Len(events):
        /\ events[i] \in MonthPassEvent
        /\ \E j \in i+1..Len(events):
            /\ events[j] \in MonthPassEvent
            /\ ~\E k \in (i + 2)..(j-1):
                events[k] \in MonthPassEvent
            \* where op is not true for all users
            /\ \E u \in USERS:
                ~op(u,i,j)

(***************************************************************************)
(* 15 When a User is Billed the system SHALL call the Bill endpoint        *)
(*    of the Payment Processor.                                            *)
(* This requirement is satisfied by how requirements 4.2.2, 12 and 13      *)
(* are tested. They test that appropriate Bill message was dispatched      *)
(***************************************************************************)

(***************************************************************************)
(* 12 When a User becomes Subscribed                                       *)
(***************************************************************************)

(***************************************************************************)
(* 12.1 they shall be Billed the Subscription Fee before the end of the    *)
(*      month                                                              *)
(***************************************************************************)

SubscribedThisMonth(u, start, end) ==
    /\ ~Subscribed(u, start) 
    /\ Subscribed(u, end-1)

UserSubscribedThisMonthBilledSubscriptionFee(u, start, end) ==
    LET shouldBill == SubscribedThisMonth(u, start, end) IN
    \* Only applies if subscribed this month
    \/ ~shouldBill
    \/ /\ shouldBill
       /\ \E i \in start..end:
            /\ events[i] \in BillEvent
            /\ events[i].user = u
            /\ events[i].fee = SubscriptionFee
    
 
SubscribedNewUsersBilledSubscriptionFee ==
    TrueForEveryUserMonth(UserSubscribedThisMonthBilledSubscriptionFee, TRUE)

(***************************************************************************)
(* 13 When a User is Subscribed at the start of a month, they shall be     *)
(*    Billed the Subscription Fee                                          *)
(***************************************************************************)
SubscribedUserBilledThisMonth(u, start, end) ==
    LET subscribed == Subscribed(u, start) IN
    \* Only applies if subscribed at start of month
    \/ ~subscribed
    \/ /\ subscribed
       /\ \/ \E i \in start..end:
                /\ events[i] \in BillEvent
                /\ events[i].user = u
                /\ events[i].fee = SubscriptionFee
         \* If the user failed a payment this is a separate workflow
          \/ \E i \in start..end: 
                /\ events[i] \in PaymentFailedEvent
                /\ events[i].user = u


SubscribedUsersBilledStartOfMonth == 
    TrueForEveryUserMonth(SubscribedUserBilledThisMonth, FALSE)

(***************************************************************************)
(* 12.2     If the requesting User has Post Due Payments they SHALL be     *)
(*          Billed in that amount before the end of the month, and         *)
(*          Post Due Payments shall be zeroed                              *)
(***************************************************************************)
(***************************************************************************)
(* 16  When a callback is received to the Payment Failed endpoint for a    *)
(*     User, the system SHALL                                              *)
(*     16.2 set Post Due Payment for the User to:                          *)
(*          (failed payment amount) + CancellationFee                      *)
(***************************************************************************)

PotentialStartingEvent(u, event) == 
    /\ event \in StartSubscriptionEvent \union
                 StartTrialEvent
    /\ event.user = u

IsPaymentFailedEvent(u, event) ==
    /\ event \in PaymentFailedEvent
    /\ event.user = u
    
UserBilledForFailureBetweenRange(u, start, end, fee) ==
    \E i \in start..end:
        /\ events[i] \in BillEvent
        /\ events[i].user = u
        /\ events[i].fee = FailedPaymentFee

UserBilledForPostDuePaymentsIfSubscribed(u, start, end) ==
    LET starts == {i \in 1..start: PotentialStartingEvent(u, events[i])} IN
    LET paymentFailed == {i \in 1..start:IsPaymentFailedEvent(u, events[i])} IN
    
    \A p \in paymentFailed:

        LET resubscribedAfterFailedPayment ==
            \E i \in p..end:
                /\ i \in starts
        IN

        \/ ~resubscribedAfterFailedPayment
        \/ /\ resubscribedAfterFailedPayment
            \* There doesn't exist a failed payment
           /\ ~\E i \in p..end:
                \* That has a subscription directly after it
                /\ i \in starts
                /\ ~\E j \in p..i:
                    j \in starts
                \* Where the user was not billed for the failed payment
                /\ ~UserBilledForFailureBetweenRange(u, i, end, events[p].fee)                               

SubscribedUsersBilledPostDuePayements ==
    TrueForEveryUserMonth(UserBilledForPostDuePaymentsIfSubscribed, TRUE)


(***************************************************************************)
(* 4 Cancel Subscription endpoint                                          *)
(* 4.2.2  if the user is Not Subscribed at the end of the current month,   *)
(* they SHALL be Billed a Cancellation Fee                                 *)
(***************************************************************************)
UserCancelledLastMonth(u, start, end) ==
    \* start - 1 because it doesn't count cancellations that take effect
    \* at start
    /\ Subscribed(u, start-1) 
    /\ ~Subscribed(u, start)

UserCancelledLastMonthBilled(u, start, end) ==
    \* Only applies if user cancelled this month
    \/ ~UserCancelledLastMonth(u, start, end)
    \/ /\ UserCancelledLastMonth(u, start, end)
       /\ \/ \E i \in start..end:
                /\ events[i] \in BillEvent
                /\ events[i].user = u
                /\ events[i].fee = CancellationFee
          \* If the user failed a payment this is a separate workflow
          \/ \E i \in start..end: 
                /\ events[i] \in PaymentFailedEvent
                /\ events[i].user = u

CancelingUsersBilledCancelationFees ==
    TrueForEveryUserMonth(UserCancelledLastMonthBilled, FALSE)


(***************************************************************************)
(* State Constraints                                                       *)
(***************************************************************************)

EventLengthLimit ==
    Len(events) < 10


MonthLimit ==
    LET monthPassEvents == SelectSeq(events, LAMBDA x: x.type = "monthpass") 
    IN
    Len(monthPassEvents) < 5

StateLimit ==
    /\ EventLengthLimit
    /\ MonthLimit

=============================================================================
\* Modification History
\* Last modified Sun Jun 19 17:43:11 MST 2022 by elliotswart
\* Created Thu Jun 16 19:34:18 MST 2022 by elliotswart