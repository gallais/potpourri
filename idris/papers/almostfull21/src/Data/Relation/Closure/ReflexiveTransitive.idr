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

export
foldr : ({x, y, z : a} -> p x y -> q y z -> q x z) ->
        ({x : a} -> q x x) ->
        RTList p ~> q
foldr c n []          = n
foldr c n (pxy :: ps) = c pxy (foldr {q} c n ps)

export
foldl : {0 p, q : Rel a} ->
        ({x, y, z : a} -> q x y -> p y z -> q x z) ->
        {x, y, z : a} -> q x y -> RTList p y z -> q x z
foldl c n []          = n
foldl c n (pxy :: ps) = foldl {q} c (c n pxy) ps

export
rtlist : (Reflexive a p, Transitive a p) => RTList p ~> p
rtlist = foldr {q = p} (transitive {rel = p}) (reflexive {rel = p})

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
