module TicTacToe.Render

import TicTacToe.Optimised
import Data.Vect
import Data.String

hline : String
hline = "-+-+-"

Show Player where
  show X = "O"
  show O = "X"

displayRow : Show a => Vect 3 (Maybe a) -> String
displayRow r = concat $ intersperse "|"
                      $ map (maybe " " show) (toList r)

BoardShape : Type -> Type
BoardShape a = Vect 3 (Vect 3 a)

[matrix] Functor BoardShape where
  map f xs = map (map f) xs

displayBoardShape : Show a => BoardShape (Maybe a) -> List String
displayBoardShape xs = intersperse hline $
  toList $ map displayRow xs

displayState : State n -> List String
displayState state = displayBoardShape state.grid

displayTurn : Player -> String
displayTurn p = "\{show p} to play: "

display : Board n -> List String
display board =
  (displayState $ snd board) `snoc`
  (displayTurn $ fst board)
