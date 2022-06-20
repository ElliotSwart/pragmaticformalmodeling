------------------------------ MODULE juniorv2 ------------------------------

(***************************************************************************)
(* Database Rows                                                           *)
(***************************************************************************)

UserRow == [
    subscribed: BOOLEAN,
    \* Forget cancelled
    inTrial: BOOLEAN,
    trialStartTime: Nat,
    billedForMonth: Nat,
    hasHadTrialOrSubscription: BOOLEAN,
    hasCancelled: BOOLEAN,
    cancelMonth: Nat
]

StartSubscription(u) ==
    \* Not subscribed
    /\ /\ database.users[u].subscribed = FALSE
       /\ \/ database.users[u].inTrial = FALSE
          \/ database.users[u].trialStartTime = month
          
    /\ database' = 
        [database EXCEPT
              !["users"][u].subscribed = TRUE,
              !["users"][u].hasHadTrialOrSubscription = TRUE,
              !["users"][u].hasCancelled = FALSE
        ]
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "startsubscription", user |-> u])
    /\ UNCHANGED month


CancelSubscription(u) ==
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
                Append(database.billQueue, 
                    [user |-> u, fee |-> CancellationFee])
        ]
                   
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "cancelsubscription", user |-> u])
    /\ UNCHANGED <<month>>

StartTrial(u) ==
    /\ database.users[u].inTrial = FALSE
    /\ database.users[u].subscribed = FALSE
    /\ database.users[u].hasHadTrialOrSubscription = FALSE
    /\ database' = [database EXCEPT
                        !["users"][u].inTrial = TRUE,
                        !["users"][u].trialStartTime = month,
                        !["users"][u].hasHadTrialOrSubscription = TRUE
                   ]
                        
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "starttrial", user |-> u])
    /\ UNCHANGED <<month>>
    

CancelTrial(u) ==
    \* In active trial
    /\ database.users[u].inTrial = TRUE
    /\ database.users[u].trialStartTime = month
    \* And not subscribed 
    /\ database.users[u].subscribed = FALSE
    /\ database' = [database EXCEPT
                        !["users"][u].inTrial = FALSE
                   ]
                   
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "canceltrial", user |-> u])
    /\ UNCHANGED <<month>>


WatchVideo(u) ==
    /\ \/ database.users[u].subscribed = TRUE
       \/ database.users[u].inTrial = TRUE
       \* Remove video access at the end of cancelled month
       \/ /\ database.users[u].hasCancelled = TRUE
          /\ database.users[u].cancelMonth = month
    
    \* Observability required by stub
    /\ events' = Append(events, [type |-> "watchvideo", user |-> u])
    /\ UNCHANGED <<month, database>>

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
                            [user |-> u, fee |-> SubscriptionFee]),
                !["users"][u].billedForMonth = month
            ]
    /\ UNCHANGED <<events, month>>


=============================================================================
\* Modification History
\* Last modified Sun Jun 19 17:44:01 MST 2022 by elliotswart
\* Created Sun Jun 19 16:56:29 MST 2022 by elliotswart
