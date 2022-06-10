---------------------------- MODULE tictactoexwin ----------------------------


XMustEventuallyWin == <>Won("X")

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


=============================================================================
