---------------------------- MODULE tictactoe ----------------------------

EXTENDS Naturals

VARIABLES 
    board, \* board[1..3][1..3] A 3x3 tic-tac-toe board
    nextTurn \* who goes next

Pieces == {"X", "O", "_"} \* "_" represents a blank square

Init ==
        /\ nextTurn = "X" \* X always goes first
        \* Every space in the board states blank
        /\ board = [i \in 1..3 |-> [j \in 1..3 |-> "_"]]

Move(player) ==
    \E i \in 1..3: \E j \in 1..3: \* There exists a position on the board
        /\ board[i][j] = "_" \* Where the board is currently empty
        (********************************************************************)
        (* The future state of board is the same, except a piece is in that *)
        (* spot                                                             *)
        (********************************************************************)
        /\ board' = [board EXCEPT
                        ![i][j] = player] 

MoveX == 
    /\ nextTurn = "X" \* Only enabled on X's turn
    /\ Move("X")
    /\ nextTurn' = "O" \* The future state of next turn is O

MoveO ==
    /\ nextTurn = "O" \* Only enabled on O's turn 
    /\ Move("O")
    /\ nextTurn' = "X" \* The future state of next turn is X

\* Every state, X will move if X's turn, O will move on O's turn
Next == MoveX \/ MoveO

\* A description of every possible game of tic-tac-toe
\* will play until the board fills up, even if someone won
Spec == Init /\ [][Next]_<<board,nextTurn>>

(***************************************************************************)
(* Invariants: The things we are checking for.                             *)
(***************************************************************************)

WinningPositions == {
    \* Horizonal wins
    {<<1,1>>, <<1,2>>, <<1,3>>},
    {<<2,1>>, <<2,2>>, <<2,3>>},
    {<<3,1>>, <<3,2>>, <<3,3>>},
    \* Vertical wins
    {<<1,1>>, <<2,1>>, <<3,1>>},
    {<<1,2>>, <<2,2>>, <<3,2>>},
    {<<1,3>>, <<2,3>>, <<3,3>>},
    \* Diagonal wins
    {<<1,1>>, <<2,2>>, <<3,3>>},
    {<<3,1>>, <<2,2>>, <<1,3>>}
}

Won(player) == 
    \* A player has won if there exists a winning position
    \E winningPosition \in WinningPositions:
        \* Where all the needed spaces
        \A neededSpace \in winningPosition:
            \* are occupied by one player
            board[neededSpace[1]][neededSpace[2]] = player

XHasNotWon == ~Won("X")
OHasNotWon == ~Won("O")

BoardFilled ==
    \* There does not exist
    ~\E i \in 1..3, j \in 1..3:
        \* an empty space
        LET space == board[i][j] IN
        space = "_"

\* It's not a stalemate if one player has won or the board is not filled
NotStalemate ==
    \/ Won("X")
    \/ Won("O")
    \/ ~BoardFilled

=============================================================================
