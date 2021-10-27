module Main

import Control.ANSI
import Data.Display
import Data.List
import Data.Matrix
import Data.Nat
import Data.Nat.Views
import Data.Relation.Binary
import Data.String
import Data.Tiling
import Data.Vect

import NCurses

%default total

fill : Nat -> (w, h : Nat) -> Tiling (Matrix Char) w h
fill r w h = Value (pure $ pure $ fromMaybe '.' $ last' $ unpack $ show r)

example : Nat -> (w, h : Nat) -> Tiling (Matrix Char) w h
example r Z h = Empty
example r w Z = Empty
example r w h
  = let (ht ** hb ** prfV) = toHalves h in
    let (wl ** wr ** prfH) = toHalves w in
    Layer $ SplitV prfV
      (Layer $ SplitH prfH (fill r wl ht) Empty)
      (Layer $ SplitH prfH Empty (assert_total $ example (S r) wr hb))

  where
    toHalves : (w : Nat) -> (wl : Nat ** wr : Nat ** w === wl + wr)
    toHalves w with (half w)
      toHalves    (wl + wl)  | HalfEven wl = (wl   ** wl ** Refl)
      toHalves (S (wl + wl)) | HalfOdd  wl = (S wl ** wl ** Refl)

main : IO ()
main = withNCurses $ do
  (rows, cols) <- getMaxSize !stdWindow
  putStrLn $ concat $ eraseScreen All :: display (example 1 cols rows)
