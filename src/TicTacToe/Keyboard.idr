module TicTacToe.Keyboard

import Data.Fin
import Data.Maybe
import Data.List
import Data.Vect
import TicTacToe.Optimised

public export
keyForPos : Grid ->  String
keyForPos (0, 0) = "q"
keyForPos (0, 1) = "w"
keyForPos (0, 2) = "e"
keyForPos (1, 0) = "a"
keyForPos (1, 1) = "s"
keyForPos (1, 2) = "d"
keyForPos (2, 0) = "z"
keyForPos (2, 1) = "x"
keyForPos (2, 2) = "c"

public export
KeyPosDictionary : List (String, Grid)
KeyPosDictionary =
  map (\u => (keyForPos u, u)) (toList positions)

public export
validateKey : String -> Maybe Grid
validateKey str = map snd
  (find ((== str) . Builtin.fst) KeyPosDictionary)

public export
posForKey : (str : String) ->
  {auto 0 isValid : IsJust (validateKey str)} -> Grid
posForKey str = fromJust $ validateKey str
