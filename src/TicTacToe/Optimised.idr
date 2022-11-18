module TicTacToe.Optimised

import Data.Fin
import Games
import Syntax.WithProof
import Data.List
import Data.DPair
import Data.Vect

import Syntax.PreorderReasoning

public export
R : Type
R = Fin 3

public export
XWin, OWin, Draw : R
XWin = 0
Draw = 1
OWin = 2

public export
data Player = X | O

public export
Eq Player where
  X == X = True
  X == O = False
  O == X = False
  O == O = True

public export
opponent : Player -> Player
opponent X = O
opponent O = X

public export
value : Player -> R
value X = XWin
value O = OWin


public export
Grid : Type
Grid = (Fin 3, Fin 3)

public export
predMod3, succMod3 : Fin 3 -> Fin 3
predMod3 FZ = 2
predMod3 (FS x) = weaken x
         -- NB: At runtime, weaken x is the identity function
         -- see 'compiled' field in the debug information by
         -- typing ':di weaken' at the REPL

succMod3 0 = 1
succMod3 1 = 2
succMod3 2 = 0

public export
rowOf, colOf : Grid -> List Grid
colOf (row, col) = [-- exclude: (row,                     col)
                    (row,            predMod3 col)
                   ,(row, predMod3 $ predMod3 col)]

rowOf (row, col) = [-- exclude: (                    row, col)
                    (           predMod3 row, col)
                   ,(predMod3 $ predMod3 row, col)]

diagsOf : Grid -> List (List Grid)
diagsOf (row, col) =
  if row == col
  then [[-- exclude: (                    row,                     col)
         (           predMod3 row,            predMod3 col)
        ,(predMod3 $ predMod3 row, predMod3 $ predMod3 col)]]
  else []
  ++
  if cast row + cast col == 2
  then [[-- exclude (                    row,                     col)
         (           predMod3 row,            succMod3 col)
        ,(predMod3 $ predMod3 row, succMod3 $ succMod3 col)]]
  else []

public export
positions : Vect 9 Grid
positions = fromList [(a,b) | a <- [0,1,2], b <- [0,1,2]]

public export
Matrix : Type
Matrix = Vect 3 $ Vect 3 $ Maybe Player

infix 7 !!
public export
(!!) : Matrix -> Grid -> Maybe Player
matrix !! (row, col) = index col $ index row matrix

public export
record State (movesLeft : Nat) where
  constructor MkState
  grid : Matrix
  free : Vect movesLeft Grid --(Subset Grid $ \pos => grid !! pos === Nothing)

public export
Board : (movesLeft : Nat) -> Type
Board movesLeft = (Player , State movesLeft)

public export
EmptyMatrix : Matrix
EmptyMatrix = replicate _ $ replicate _ Nothing

indexReplicate : (x : a) ->
  (i : Fin n) -> index i (replicate n x) === x
indexReplicate x FZ = Refl
indexReplicate x (FS y) = indexReplicate x y

-- Can't be bothered...
allEmpty : (pos : Grid) -> EmptyMatrix !! pos === Nothing
allEmpty (0, 0) = Refl
allEmpty (0, 1) = Refl
allEmpty (0, 2) = Refl
allEmpty (1, 0) = Refl
allEmpty (1, 1) = Refl
allEmpty (1, 2) = Refl
allEmpty (2, 0) = Refl
allEmpty (2, 1) = Refl
allEmpty (2, 2) = Refl

public export
board0 : Board 9
board0 = ( X
         , MkState EmptyMatrix
                   positions
         )

winningMoveFor : Player -> Matrix -> Grid -> Bool
winningMoveFor p grid pos =
  any
    (\poss => all (\pos' => grid !! pos' == Just p) poss)
    (colOf pos :: rowOf pos :: diagsOf pos)

Move : {n : Nat} -> (0 board : Board n) -> Type
Move board = Fin n

drop' : (xs : List a) -> Fin (length xs) -> List a
drop' [] FZ impossible
drop' [] (FS x) impossible
drop' (x :: xs) FZ = xs
drop' (x :: xs) (FS i) = x :: drop' xs i

playAt : Grid -> Player -> Matrix -> Matrix
playAt (row,col) p grid =
  updateAt row (updateAt col (const $ Just p)) grid

play : (b : Board (S n)) -> Move b -> Board n
play (p, state) i =
  let pos = (index i state.free)
  in (opponent p
     , MkState (playAt pos p state.grid)
               (deleteAt i state.free))
TTT : {n : Nat} -> (board : Board n) -> Tree
TTT {n = 0  } _ = []
TTT {n = S n} b@(p, state) = Fin (S n) ::
  (\m => if winningMoveFor p state.grid (index m state.free)
         then []  -- Game over, p won
         else TTT (play b m))

outcome : {n : Nat} -> (b : Board n) -> Path (TTT b) -> R
outcome  {n = 0} b foo = Draw
outcome  {n = S n} (p, state) (m :: ms)
  with (winningMoveFor p state.grid (index m state.free))
 outcome {n = S n} (p, state) (m :: ms) | True  = value p
 outcome {n = S n} (p, state) (m :: ms) | False =
   outcome (play (p, state) m) ms

rangeFromBy : (Fin m) -> Vect n a -> Vect n (Fin $ m + n)
rangeFromBy x [] = []
rangeFromBy start (y :: xs) =
  -- weakenN is identity at runtime
  (replace {p = Fin} (plusSuccRightSucc _ _)
    $ weakenN _ $ FS start)
  --(weakenN _ (replace {p = Fin} (?h1) $ FS start))
    :: replace {p = Vect _ . Fin}
                          (plusSuccRightSucc _ _)
                          (rangeFromBy (FS start) xs)


argmin,argmax : (p : Player) -> (state : State n) ->
  (Move (p,state)) -> J {R} (Move (p,state))
argmax {n = 0} _ _ _ impossible
argmax {n = S n} p (MkState grid state@(curPos :: restMoves)) _ val =
  -- Somewhat silly, but since this loop is hot, forget
  -- about the given move and start with the first one
  argmax_aux FZ (val 0) (rangeFromBy {m = 1} 0 restMoves)
  where
    argmax_aux : Fin (S n) -> R -> Vect m (Fin (S n)) -> Fin (S n)
    argmax_aux curPos curVal [] = curPos
    argmax_aux curPos curVal (pos :: rest) =
      case val pos of
        2   => curPos
        val => if val > curVal
               then argmax_aux    pos    val rest
               else argmax_aux curPos curVal rest

argmin {n = 0} _ _ _ impossible
argmin {n = S n} p (MkState grid state@(curPos :: restMoves)) _ val =
  -- Somewhat silly, but since this loop is hot, forget
  -- about the given move and start with the first one
  argmin_aux FZ (val 0) (rangeFromBy {m = 1} 0 restMoves)
  where
    argmin_aux : Fin (S n) -> R -> Vect m (Fin (S n)) -> Fin (S n)
    argmin_aux curPos curVal [] = curPos
    argmin_aux curPos curVal (pos :: rest) =
      case val pos of
        0   => curPos
        val => if val < curVal
               then argmin_aux    pos    val rest
               else argmin_aux curPos curVal rest


selection : (p : Player) -> (a : State n) -> Move (p, a) -> J {R} (Move (p,a))
selection X a move = argmin X a move
selection O a move = argmax O a move

quantifier : (p : Player) -> (a : State n) ->
  Maybe (Move (p, a)) -> K {R} (Move (p, a))
quantifier p a (Just move) = overline (selection p a move)
quantifier p a (Nothing) = const Draw

AnyMove : (p : Player) -> (a : State n) -> Maybe (Move (p, a))
AnyMove p a = case a.free of
  [] => Nothing
  (x :: xs) => Just 0

selections : {k : Nat} -> (b : Board k) -> 𝓙 {R} (TTT b)
selections {k = 0  } b = []
selections {k = S k} (p, state) =
  selection p state FZ :: \m =>
    case @@(winningMoveFor p state.grid (index m state.free)) of
        (True  ** prf) => rewrite prf in []
        (False ** prf) => rewrite prf in
          selections _

quantifiers : {k : Nat} -> (b : Board k) -> 𝓚 {r = R} (TTT b)
quantifiers b = Overline (selections b)

TicTacToe : Game {R}
TicTacToe = MkGame
              (TTT board0)
              (outcome board0)
              (quantifiers board0)

r : R
r = optimalOutcome TicTacToe

s2 : Path (TTT Optimised.board0)
s2 = strategicPath
  (selectionStrategy (selections board0)
                     (TicTacToe .q))

printPath : {n : Nat} -> {b : Board n} ->
  Path (TTT {n} b) -> String
printPath {n = 0  } {b = (p,state)} x = "!"
printPath {n = S n} {b = (p,state)} (u :: us)=
  "\{show $ index u state.free}"
  ++
  case @@(winningMoveFor p state.grid (index u state.free)) of
   (True ** prf) => "!"
   (False ** prf) => (printPath {b = play (p,state) u} $
     believe_me us) {-
     replace
       { x = (winningMoveFor p state.grid (index u state.free))
       , y = False
       , p = \v =>
       Path (if v then [] else TTT (play (p,state) u))}
         (?prff) us)-}

export
main : IO ()
main = do
  putStrLn "Starting computation"
  putStrLn $ printPath {b = board0} s2
  putStrLn $ show r
