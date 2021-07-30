module Data.Relation.Closure.Transitive

import Control.Relation
import Data.Relation
import Data.Relation.Closure.ReflexiveTransitive

%default total

public export
data TList : Rel a -> Rel a where
  (::) : {0 r : Rel a} -> {y : a} -> r x y -> RTList r y z -> TList r x z

export
forget : TList r x y -> RTList r x y
forget (x :: xs) = x :: xs

namespace TT

  export
  (++) : TList r x y -> TList r y z -> TList r x z
  (x :: xs) ++ ys = x :: xs ++ forget ys

namespace TRT

  export
  (++) : TList r x y -> RTList r y z -> TList r x z
  (x :: xs) ++ ys = x :: xs ++ ys

namespace RTT

  export
  (++) : RTList r x y -> TList r y z -> TList r x z
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: xs ++ forget ys

export
concat : TList (TList r) ~> TList r
concat (xs :: xss) = xs ++ concat (map forget xss)

{-
export
gmap : (f : a -> b) -> p ~> (q `on` f) -> TList p ~> (TList q `on` f)
gmap _ f [] = []
gmap _ f (x :: xs) = f x :: gmap _ f xs

export
map : (p ~> q) -> TList p ~> TList q
map = gmap id

export
reverseAcc : {y : a} -> (r ~> flip s) ->
             flip (TList s) x y -> TList r y z ->
             flip (TList s) x z
reverseAcc f acc [] = acc
reverseAcc f acc (x :: xs) = reverseAcc f (f x :: acc) xs

export
reverse : (r ~> flip s) -> TList r ~> flip (TList s)
reverse f = reverseAcc f []
-}
