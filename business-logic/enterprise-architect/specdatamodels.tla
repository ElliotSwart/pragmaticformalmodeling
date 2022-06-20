--------------------------- MODULE specdatamodels ---------------------------
\* This module will be imported into every implementation

EXTENDS Sequences

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
    
    
    
=============================================================================
\* Modification History
\* Last modified Fri Jun 17 00:07:38 MST 2022 by elliotswart
\* Created Thu Jun 16 20:19:00 MST 2022 by elliotswart
