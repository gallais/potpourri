module Relation.Binary.Closure.Transitive

%default total

public export
Rel : Type -> Type
Rel a = (x, y : a) -> Type

||| @Closure provides the transitive closure of its argument
export
data Closure : (r : Rel a) -> Rel a where
  One : {0 r : Rel a} -> r x y -> Closure r x y
  Add : Closure r x y -> Closure r y z -> Closure r x z

prefix 5 ^

export
(^) : {0 r : Rel a} -> r x y -> Closure r x y
(^) = One

export
add : Closure r x y -> Closure r y z -> Closure r x z
add = Add

infixl 4 |>

export
(|>) : {0 r : Rel a} -> Closure r x y -> r y z -> Closure r x z
t |> r = add t (^ r)

infix 4 <|

public export
data ViewL : (r : Rel a) -> Rel a where
  OneL : {0 r : Rel a} -> r x y -> ViewL r x y
  (<|) : {0 r : Rel a} -> r x y -> Closure r y z -> ViewL r x z

public export
viewL : Closure r x y -> ViewL r x y
viewL (One r) = OneL r
viewL (Add s t) = go s t where

  go : Closure r a b -> Closure r b c -> ViewL r a c
  go (One r) acc = r <| acc
  go (Add l r) acc = go l (Add r acc)

public export
foldl1 : {0 r, acc : Rel a} ->
         (forall x, y. r x y -> acc x y) ->
         (forall x, y, z. acc x y -> r y z -> acc x z) ->
         forall x, y. Closure r x y -> acc x y
foldl1 one add clos = case viewL clos of
  OneL r  => one r
  r <| rs => go (one r) rs where

    go : forall x, y, z. acc x y -> Closure r y z -> acc x z
    go acc (One r) = add acc r
    go acc (Add l r) = go (go acc l) r
