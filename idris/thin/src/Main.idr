module Main

import Data.Nat
import Thin

test : List (sx : SnocList Nat ** Th sx ([<] <>< [0..10]))
test = flip map [2..5] $ \ i =>
        which (\ n => n `mod` i /= 0) ([<] <>< [0..10])

main : IO ()
main = for_ test $ \ (sx ** th) =>
  case view th of
    _  => putStrLn (show th)
