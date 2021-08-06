module Data.Relation

import Control.Relation

%default total

infixr 1 ~>

public export
0 (~>) : Rel a -> Rel a -> Type
p ~> q = {x, y : a} -> p x y -> q x y

public export
0 Or : Rel a -> Rel a -> Rel a
Or p q = \x, y => Either (p x y) (q x y)

public export
0 And : Rel a -> Rel a -> Rel a
And p q = \x, y => (p x y, q x y)

public export
0 Not : Rel a -> Rel a
Not p = \x, y => Not (p x y)

public export
0 Const : Type -> Rel a
Const p = \x, y => p
