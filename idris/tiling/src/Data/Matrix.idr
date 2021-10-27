module Data.Matrix

import Control.ANSI
import Data.Display
import Data.Relation.Binary
import Data.SnocList
import Data.String
import Data.Tiling
import Data.Vect
import Syntax.PreorderReasoning

%default total

public export
0 Matrix : Type -> Sized
Matrix a w h = Vect h (Vect w a)

export
Cutting (Matrix a) (Matrix a) where
  splitH Refl = unzipWith (splitAt ?)
  splitV Refl = splitAt ?

infixr 8 +~
(+~) : Nat -> Nat -> Nat
Z   +~ n = n
S m +~ n = m +~ S n

data SnocVect : Nat -> Type -> Type where
  Lin  : SnocVect Z a
  (:<) : SnocVect n a -> a -> SnocVect (S n) a

(<>>) : SnocVect m a -> Vect n a -> Vect (m +~ n) a
[<]       <>> xs = xs
(sx :< x) <>> xs = sx <>> (x :: xs)

samePlus : (m, n : Nat) -> m +~ n === m + n
samePlus Z n = Refl
samePlus (S m) n = Calc $
  |~ S m +~ n
  ~~ m +~ S n ...( Refl )
  ~~ m + S n  ...( samePlus m (S n) )
  ~~ S m + n  ...( sym $ plusSuccRightSucc m n )

||| Compute a diff as a tiling
||| * Empty    is content that is kept the same
||| * Value v  is content that is overwritten
||| Here we proceed on the basis of either preserving or changing a full
||| line. A more subtle algorithm finding the biggest rectangles of
||| preserved content would be nice to have.
diffBy : {h : Nat} -> (a -> b -> Bool) ->
  Matrix a w h -> Matrix b w h ->
  Tiling (Matrix b) w h
diffBy eq = drop 0 where

  drop : {h : Nat} -> (n : Nat) ->
         Matrix a w h -> Matrix b w h ->
         Tiling (Matrix b) w (n +~ h)
  keep : {h : Nat} -> {n : Nat} -> SnocVect n (Vect w b) ->
         Matrix a w h -> Matrix b w h ->
         Tiling (Matrix b) w (n +~ h)

  drop n [] bs = Empty
  drop n (a :: as) (b :: bs)
    = if all (uncurry eq) (zip a b)
        then drop (S n) as bs
        else Layer $ SplitV (samePlus n ?) Empty
           $ keep [< b] as bs

  keep acc []        bs        = Value (acc <>> [])
  keep acc (a :: as) (b :: bs)
      = if all (uncurry eq) (zip a b)
        then keep (acc :< b) as bs
        else Layer $ SplitV aux (Value (acc <>> []))
           $ drop 1 as bs
   where
     aux : n +~ S m === (n +~ 0) + (S m)
     aux = Calc $
       |~ n +~ S m
       ~~ n + S m        ...( samePlus n (S m) )
       ~~ (n + Z) + S m  ...( cong (+ S m) (sym $ plusZeroRightNeutral n) )
       ~~ (n +~ Z) + S m ...( cong (+ S m) (sym $ samePlus n Z) )

export
Display (Matrix Char) where
  displayAt pos [] = []
  displayAt pos (l :: ls)
    = cursorMove (S pos.lineNo) (S pos.colnNo)
    :: pack (toList l)
    :: displayAt {t = Matrix Char} ({ lineNo $= S } pos) ls
