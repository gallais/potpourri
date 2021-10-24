module Data.Display

import Data.Relation.Binary

%default total

public export
record Position where
  constructor MkPosition
  lineNo : Nat
  colnNo : Nat

public export
interface Display (0 t : Sized) where
  displayAt : Position -> t w h -> List String
  display   : t w h -> List String
  display = displayAt (MkPosition Z Z)
