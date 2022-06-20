----------------------------- MODULE principal -----------------------------
(***************************************************************************)
(* Redeclaration of specdatamodels variables                               *)
(***************************************************************************)
EXTENDS Sequences, Naturals, FiniteSets

CONSTANT USERS

CONSTANTS
    SubscriptionFee,
    CancellationFee,
    FailedPaymentFee

VARIABLES
    month,
    database,
    events 

vars == <<events, month, database>>

INSTANCE specdatamodels

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
(*
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
*)

=============================================================================
\* Modification History
\* Last modified Sun Jun 19 17:45:52 MST 2022 by elliotswart
\* Created Fri Jun 17 00:28:26 MST 2022 by elliotswart
