module Data.Relation.Closure.ReflexiveTransitive

import Control.Relation
import Data.Relation

%default total

public export
data RTList : Rel a -> Rel a where
  Nil  : RTList r x x
  (::) : {0 r : Rel a} -> {y : a} -> r x y -> RTList r y z -> RTList r x z

export
reflexive : (===) ~> RTList r
reflexive Refl = []

export
(++) : RTList r x y -> RTList r y z -> RTList r x z
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

export
concat : RTList (RTList r) ~> RTList r
concat [] = []
concat (xs :: xss) = xs ++ concat xss

export
gmap : (f : a -> b) -> p ~> (q `on` f) -> RTList p ~> (RTList q `on` f)
gmap _ f [] = []
gmap _ f (x :: xs) = f x :: gmap _ f xs

export
map : (p ~> q) -> RTList p ~> RTList q
map = gmap id

{-
export
reverseAcc : {y : a} -> (r ~> flip s) ->
             flip (RTList s) x y -> RTList r y z ->
             flip (RTList s) x z
reverseAcc f acc [] = acc
reverseAcc f acc (x :: xs) = reverseAcc f (f x :: acc) xs

export
reverse : (r ~> flip s -> RTList r ~> flip (RTList s)
reverse f = reverseAcc f []
-}
