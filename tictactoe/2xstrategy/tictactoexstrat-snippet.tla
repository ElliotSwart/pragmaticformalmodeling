---------------------------- MODULE tictactoexstrat ----------------------------

MoveX ==
    /\ nextTurn = "X" \* Only enabled on X's turn
    /\ ~Won("O") \* And X has not won
    \* This specifies the spots X will move on X's turn
    /\ \/ /\ BoardEmpty
          /\ StartInCorner
       \/ /\ ~BoardEmpty \* If it's not the start
          /\ \/ /\ CanWin
                /\ Win
             \/ /\ ~CanWin
                /\  \/ /\ CanBlockWin
                       /\ BlockWin
                    \/ /\ ~CanBlockWin
                       /\ \/ /\ CanTakeCenter
                             /\ TakeCenter
                          \/ /\ ~CanTakeCenter
                             /\ \/ /\ CanSetupWin
                                   /\ SetupWin
                                \/ /\ ~CanSetupWin
                                   /\ MoveToEmpty("X") \* No more strategies. Pick spot
    /\ nextTurn' = "O" \* The future state of next turn is O

=============================================================================