module Main

import Control.ANSI
import Data.Display
import Data.Matrix
import Data.Nat
import Data.Nat.Views
import Data.Relation.Binary
import Data.Tiling
import Data.Vect

%default total

fill : (w, h : Nat) -> Tiling (Matrix Char) w h
fill w h = Value (pure $ pure '.')

example : (w, h : Nat) -> Tiling (Matrix Char) w h
example Z h = Empty
example w Z = Empty
example w h
  = let (ht ** hb ** prfV) = toHalves h in
    let (wl ** wr ** prfH) = toHalves w in
    Layer $ SplitV prfV
      (Layer $ SplitH prfH (fill wl ht) Empty)
      (Layer $ SplitH prfH Empty (assert_total $ example wr hb))

  where
    toHalves : (w : Nat) -> (wl : Nat ** wr : Nat ** w === wl + wr)
    toHalves w with (half w)
      toHalves    (wl + wl)  | HalfEven wl = (wl   ** wl ** Refl)
      toHalves (S (wl + wl)) | HalfOdd  wl = (S wl ** wl ** Refl)


main : IO ()
main = putStrLn $ concat $ eraseScreen All :: display (example 32 32)
