module TicTacToe

import Data.Fin
import Games

R : Type
R = Fin 3

XWin, OWin, Draw : R
XWin = 0
Draw = 1
OWin = 2

data Player = X | O

opponent : Player -> Player
opponent X = O
opponent O = X

value : Player -> R
value X = XWin
value O = OWin

Grid, Matrix, Board : Type
Grid = (Fin 3, Fin 3)
Matrix = Grid -> Maybe Player
Board = (Player , Matrix)

board0 : Board
board0 = (X , const Nothing)

wins : Player -> Matrix -> Bool
wins p a = line || col || diag
  where
    is : Maybe Player -> Player -> Bool
    Nothing `is` p = False
    (Just X) `is` X = True
    (Just X) `is` O = False
    (Just O) `is` X = False
    (Just O) `is` O = True

    l0, l1, l2, c0, c1, c2, d0, d1, d2,
    line, col, diag : Lazy Bool

    l0 = (a (0, 0) `is` p) && (a (0, 1) `is` p) && (a (0, 2) `is` p)
    l1 = (a (1, 0) `is` p) && (a (1, 1) `is` p) && (a (1, 2) `is` p)
    l2 = (a (2, 0) `is` p) && (a (2, 1) `is` p) && (a (2, 2) `is` p)

    line = l0 || l1 || l2

    c0 = (a (0, 0) `is` p) && (a (1, 0) `is` p) && (a (2, 0) `is` p)
    c1 = (a (0, 1) `is` p) && (a (1, 1) `is` p) && (a (2, 1) `is` p)
    c2 = (a (0, 2) `is` p) && (a (1, 2) `is` p) && (a (2, 2) `is` p)

    col = c0 || c1 || c2

    d0 = (a (0, 0) `is` p) && (a (1, 1) `is` p) && (a (2, 2) `is` p)
    d1 = (a (2, 0) `is` p) && (a (1, 1) `is` p) && (a (0, 2) `is` p)

    diag = d0 || d1

Move : Board -> Type
Move pa = DPair Grid (\pos => snd pa pos === Nothing)

update : (p : Player) -> (a : Matrix) -> Move (p , a) -> Matrix
update p a (pos0 ** _) = \pos =>
  if pos0 == pos
  then Just p
  else a pos

play : (b : Board) -> Move b -> Board
play (p, a) move = (opponent p , update p a move)

TTT : Board -> Nat -> Tree
TTT _ 0 = []
TTT b@(p, a) (S n) =
  if wins (opponent p) a
  then []
  else (Move b) :: (\m => TTT (play b m) n)

outcome : (b : Board) -> (k : Nat) -> Path (TTT b k) -> R
outcome b 0 foo = Draw
outcome  (p, a) (S k) ms with (wins (opponent p) a)
 outcome (p, a) (S k) ms | True = value (opponent p)
 outcome (p, a) (S k) (m :: ms) | False =
   outcome (play (p, a) m) k ms
