-------------------------------- MODULE specjuniorv1 --------------------------------
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

UserRow == [
    subscribed: BOOLEAN,
    \* Forget canceled
    inTrial: BOOLEAN,
    trialStartTime: Nat,
    billedForMonth: Nat
]

BillQueueItem == [
    user: USERS,
    fee: Fees
]

TypeOk ==
    /\ EventsOk
    /\ month \in Month
    /\ database.users \in [USERS -> UserRow]
    /\ database.billQueue \in Seq(BillQueueItem)

    
(***************************************************************************)
(* API endpoints                                                           *)
(***************************************************************************)


StartSubscription(u) ==
    /\ database.users[u].subscribed = FALSE
    /\ database' = [database EXCEPT
                        !["users"][u].subscribed = TRUE
                   ]
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "startsubscription", user |-> u])
    /\ UNCHANGED month


CancelSubscription(u) ==
    /\ database.users[u].subscribed = TRUE
    /\ database' = 
        [database EXCEPT
            !["users"][u].subscribed = FALSE,
            \* Charge cancellation fee
            !["billQueue"] = 
                Append(database.billQueue, 
                    [user |-> u, fee |-> CancellationFee])
        ]
                   
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "cancelsubscription", user |-> u])
    /\ UNCHANGED <<month>>

    
StartTrial(u) ==
    /\ database.users[u].inTrial = FALSE
    /\ database.users[u].subscribed = FALSE
    /\ database' = [database EXCEPT
                        !["users"][u].inTrial = TRUE]
                        
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "starttrial", user |-> u])
    /\ UNCHANGED <<month>>
    

CancelTrial(u) ==
    /\ database.users[u].inTrial = TRUE
    /\ database' = [database EXCEPT
                        !["users"][u].inTrial = FALSE
                   ]
                   
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "canceltrial", user |-> u])
    /\ UNCHANGED <<month>>


WatchVideo(u) ==
    /\ \/ database.users[u].subscribed = TRUE
       \/ database.users[u].inTrial = TRUE
    
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "watchvideo", user |-> u])
    /\ UNCHANGED <<month, database>>

\* Stub method, do not change
Bill(u, fee) ==
    /\ events' = Append(events, [type |-> "bill", 
                                 user |-> u, 
                                 fee |-> fee])

PaymentFailed(u, fee) ==
    /\ database' = [database EXCEPT
                        !["users"][u].subscribed = FALSE
                   ]
    
    \* Observability required by stub
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


BillSubscribedUsers ==
    \E u \in USERS:
        \* That is subscribed
        /\ \/ database.users[u].subscribed = TRUE
           \* Subscribed from a trial so bill
           \/ /\ database.users[u].inTrial = TRUE
              /\ database.users[u].trialStartTime < month
        \* Ensure users are not double billed
        /\ database.users[u].billedForMonth < month
        /\ database' = 
            [database EXCEPT
                \* Add subscription fee
                !["billQueue"] = 
                    Append(database.billQueue, 
                            [user |-> u, fee |-> SubscriptionFee]),
                !["users"][u].billedForMonth = month
            ]

ProcessBills ==
    /\ Len(database.billQueue) > 0
    /\ LET bill == Head(database.billQueue) IN
        \* Bills user
        /\ Bill(bill.user, bill.fee)
        /\ database' = 
            [database EXCEPT
                \* Removes head of queue
                !["billQueue"] = 
                    SubSeq(database.billQueue, 
                    2, Len(database.billQueue))
            ]

(***************************************************************************)
(* Stub method that prevents the month from passing until all operations   *)
(* are complete. Represent worker methods, etc.                            *)
(***************************************************************************)
HandledMonth ==
    /\ ~ENABLED BillSubscribedUsers
    /\ ~ENABLED ProcessBills

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
    /\ events = <<>> \* Events must be initialized empty, per stub
    /\ month = 0
    /\ database = [
            \* Users start with everything unset
            users |-> 
                [u \in USERS |-> 
                   [
                    subscribed |-> FALSE,
                    inTrial |-> FALSE,
                    trialStartTime |-> 0,
                    billedForMonth |-> 0
                   ]
                ],
            \* Bill queue starts empty
            billQueue |-> <<>>
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
            \* Add more user based states
    \* Payment failing behavior is part of spec not implementation
    \/ ExistingBillFailed
    \/ BillSubscribedUsers

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