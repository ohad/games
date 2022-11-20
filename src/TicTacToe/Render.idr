module TicTacToe.Render

import TicTacToe.Optimised
import TicTacToe.Keyboard
import Data.Vect
import Data.String
import System
import System.File
import Syntax.WithProof
import Games

export
Show Player where
  show X = "X"
  show O = "O"

hline : String
hline = "-+-+-"

displayRow : Show a => Vect 3 (Maybe a) -> String
displayRow r = concat $ intersperse "|"
                      $ map (maybe " " show) (toList r)

displayBoardShape : Show a => BoardShape (Maybe a) -> List String
displayBoardShape xs = intersperse hline $
  toList $ map displayRow xs

[StringShow] Show String where
  show x = x

displayState : State n -> List String
displayState state = displayBoardShape state.grid

displayTurn : Player -> String
displayTurn p = "\{show p} to play."

movesOnGrid : List Grid -> BoardShape (Maybe String)
movesOnGrid xs = foldl
  (\grid,pos => updateBoard pos (Just $ keyForPos pos) grid)
  EmptyBoard xs

infixl 6 `snoc`

export
display : {n : Nat} -> Board n -> List String
display board =
  (displayState $ snd board) ++
  (if n > 0 then [(displayTurn $ fst board)]
            else [])
  ++ ("":: "Available moves" ::
  (displayBoardShape @{StringShow} (movesOnGrid $ toList (snd board).free)))


export
printPath : {n : Nat} -> {b : Board n} ->
  Path (TTT {n} b) -> String
printPath {n = 0  } {b = (p,state)} x = "Draw!"
printPath {n = S n} {b = (p,state)} (u :: us)
  with (winningMoveFor p state.grid (index u state.free))
 printPath {n = S n} {b = (p,state)} (u :: us) | True =
   "\{show p}:\{show $ index u state.free}; \{show p} won."
 printPath {n = S n} {b = (p,state)} (u :: us) | False =
   "\{show p}:\{show $ index u state.free};"
   ++ (printPath us)



partial
prompt : (b : Board n) -> IO (Move b)
prompt b = do
  putStr "Your move: "
  c <- getLine
  let Just pos = validateKey (cast c)
  | Nothing => do putStrLn "Invalid key \{cast {to = String} c}. Try again."
                  prompt b
  let Just move = findIndex (== pos) (snd b).free
  | Nothing => do putStrLn "Illegal move \{cast {to = String} c}. Try again."
                  prompt b
  pure move


hack : {n : Nat} -> (b : Board (S n)) -> Move b ->
  (continuation : {n : Nat} -> (b' : Board n) -> IO ()) -> IO ()
hack b@(p,state) move continuation
  with (play b move)
     | (winningMoveFor p state.grid (index move state.free))
 hack b@(p,state) move continuation | b' | False = continuation b'
 hack b@(p,state) move continuation | b' | True = do
   _ <- system "clear"
   putStrLn $ unlines $ display b'
   putStrLn "\{show p} wins."


partial
playBothSides : {n : Nat} -> (b : Board n) -> IO ()
playBothSides b = do
  _ <- system "clear"
  putStrLn $ unlines $ display b
  let (S k) = n
  | Z => putStrLn "Draw!"
  move <- prompt b
  hack b move playBothSides

spath : {n : Nat} -> (b : Board n) -> Path (TTT b)
spath b = strategicPath
  (selectionStrategy (selections b)
                     (outcome b))

partial
playAI : {default False isAI : Bool} ->
  {n : Nat} -> (b : Board n) -> IO ()
playAI {isAI = False} b = do
  _ <- system "clear"
  putStrLn $ unlines $ display b
  let (S k) = n
  | Z => putStrLn "Draw!"
  move <- prompt b
  hack b move (playAI {isAI = True})
playAI {isAI = True} b@(p,state) = do
  _ <- system "clear"
  putStrLn $ unlines $ display b
  fflush stdout
  let (S k) = n
  | Z => putStrLn "Draw!"
  let move :: _ = spath (p,state)
  hack b move (playAI {isAI = False})

r : R
r = optimalOutcome TicTacToe

ProblematicMatrix : Matrix
ProblematicMatrix =
  [[Just X, Just O, Just X]
  ,[Just O, Just X, Nothing]
  ,[Just O, Nothing, Nothing]
  ]

FreeMoves : Matrix -> List Grid
FreeMoves grid = [pos | pos <- toList positions, isNothing (grid !! pos) ]

SizeMakeBoard : Matrix -> Nat
SizeMakeBoard grid = length (FreeMoves grid)

MakeBoard : (p : Player) -> (grid : Matrix) -> Board (SizeMakeBoard grid)
MakeBoard p grid = (p, MkState grid (fromList $ FreeMoves grid))

ProblematicBoard : Board ?
ProblematicBoard = MakeBoard X ProblematicMatrix

main : IO ()
main = do
  --putStrLn "Starting computation"
  --putStrLn $ printPath {b = board0}
  --                     (spath board0)
  playAI board0
  pure ()
