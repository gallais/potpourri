module Data.Relation

import Control.Relation

%default total

infixr 1 ~>

public export
0 (~>) : Rel a -> Rel a -> Type
p ~> q = {x, y : a} -> p x y -> q x y
