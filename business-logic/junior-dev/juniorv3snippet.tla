------------------------------ MODULE juniorv3 ------------------------------

(***************************************************************************)
(* Database Rows                                                           *)
(***************************************************************************)

UserRow == [
    subscribed: BOOLEAN,
    \* Forget canceled
    inTrial: BOOLEAN,
    trialStartTime: Nat,
    billedForMonth: Nat,
    hasHadTrialOrSubscription: BOOLEAN,
    hasCancelled: BOOLEAN,
    cancelMonth: Nat,
    subscribeMonth: Nat
]
    
(***************************************************************************)
(* API endpoints                                                           *)
(***************************************************************************)


StartSubscription(u) ==
    \* Not subscribed
    /\ /\ database.users[u].subscribed = FALSE
       /\ \/ database.users[u].inTrial = FALSE
          \/ database.users[u].trialStartTime = month
          
    /\ database' = 
        [database EXCEPT
              !["users"][u].subscribed = TRUE,
              !["users"][u].hasHadTrialOrSubscription = TRUE,
              !["users"][u].hasCancelled = FALSE,
              !["users"][u].inTrial = FALSE,
              !["users"][u].subscribeMonth = month,
              !["billQueue"] = 
                    Append(database.billQueue, 
                        [user |-> u, 
                        fee |-> SubscriptionFee,
                        when |-> month])
        ]
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "startsubscription", user |-> u])
    /\ UNCHANGED month


CancelSubscription(u) ==
    LET updatedBillQueue == 
        IF \E i \in 1..Len(database.billQueue):
            /\ database.billQueue[i].user = u
            /\ database.billQueue[i].fee = SubscriptionFee
        THEN database.billQueue
        ELSE Append(database.billQueue, 
                [user |-> u, fee |-> SubscriptionFee, when |-> month])
    IN
    
    \* Subscribed
    /\ \/ database.users[u].subscribed = TRUE
       \/ /\ database.users[u].inTrial = TRUE
          /\ database.users[u].trialStartTime < month
    /\ database' = 
        [database EXCEPT
            !["users"][u].subscribed = FALSE,
            !["users"][u].inTrial = FALSE,
            !["users"][u].hasCancelled = TRUE,
            !["users"][u].cancelMonth = month,

            \* Charge cancellation fee
            !["billQueue"] = 
                Append(updatedBillQueue, 
                    [user |-> u, 
                     fee |-> CancellationFee,
                     when |-> month + 1])
        ]
                   
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "cancelsubscription", user |-> u])
    /\ UNCHANGED <<month>>


(***************************************************************************)
(* Recurring Operations                                                    *)
(***************************************************************************)

BillSubscribedUsers ==
    /\ \E u \in USERS:
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
                            [user |-> u, 
                            fee |-> SubscriptionFee,
                            when |-> month]),
                !["users"][u].billedForMonth = month
            ]
    /\ UNCHANGED <<events, month>>

ProcessBills ==
    /\ Len(database.billQueue) > 0
    /\ \E i \in 1..Len(database.billQueue):
        LET bill == database.billQueue[i] IN
        /\ bill.when = month
        \* Charge cancellation fees only a month after canceled
        \* and still canceled
        /\  \/ bill.fee # CancellationFee
            \/ /\ bill.fee = CancellationFee
               /\ \/ database.users[bill.user].subscribed = FALSE
                  \* Subscribed too late to cancel cancellation fee
                  \/database.users[bill.user].subscribeMonth >= bill.when
               
        /\ Bill(bill.user, bill.fee)
        /\ database' = 
            [database EXCEPT
                \* Removes head of queue
                !["billQueue"] = 
                    SubSeq(database.billQueue, 1, i-1) \o 
                    SubSeq(database.billQueue, i+1, Len(database.billQueue))
            ]
    /\ UNCHANGED <<month>>

=============================================================================
\* Modification History
\* Last modified Sun Jun 19 17:55:27 MST 2022 by elliotswart
\* Created Sun Jun 19 16:56:29 MST 2022 by elliotswart

