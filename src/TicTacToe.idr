module TicTacToe

import Data.Fin
import Games
import Syntax.WithProof
import Data.List

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

positions : List Grid
positions = [(a,b) | a <- [0,1,2], b <- [0,1,2]]

argmin,argmax : (p : Player) -> (a : Matrix) -> (Move (p,a)) ->
  J {R} (Move (p,a))
argmin p a move val =
  foldl (\cur, pos => case @@(a pos) of
      (Nothing ** prf) =>
        if val (pos ** prf) < val cur
        then (pos ** prf)
        else cur
      (Just x ** prf) => cur)
    move positions

argmax p a move val =
  foldl (\cur, pos => case @@(a pos) of
      (Nothing ** prf) =>
        if val (pos ** prf) > val cur
        then (pos ** prf)
        else cur
      (Just x ** prf) => cur)
    move positions

selection : (p : Player) -> (a : Matrix) -> Move (p, a) -> J {R} (Move (p,a))
selection X a move = argmin X a move
selection O a move = argmax O a move

quantifier : (p : Player) -> (a : Matrix) ->
  Maybe (Move (p, a)) -> K {R} (Move (p, a))
quantifier p a (Just move) = overline (selection p a move)
quantifier p a (Nothing) = const Draw

AnyMove : (p : Player) -> (a : Matrix) -> Maybe (Move (p, a))
AnyMove p a =
  let u = find (\pos => isNothing (a pos)) positions
  in ?AnyMove_rhs

quantifiers : (b : Board) -> (k : Nat) -> 𝓚 {r = R} (TTT b k)
quantifiers b 0 = []
quantifiers  (p,a) (S k) with (wins (opponent p) a)
 quantifiers (p,a) (S k) | True = []
 quantifiers (p,a) (S k) | False =
   quantifier p a (AnyMove p a) :: (\move => quantifiers (play (p,a) move) k)

ticTacToe : Game {R}
ticTacToe = MkGame (TTT board0 9)
              (outcome board0 9) (quantifiers board0 9)

r : R
r = optimalOutcome ticTacToe
