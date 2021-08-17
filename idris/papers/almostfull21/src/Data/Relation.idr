module Data.Relation

import Control.Relation

%default total

infixr 1 ~>

public export
0 (~>) : Rel a -> Rel a -> Type
p ~> q = {i, j : a} -> p i j -> q i j

public export
0 Or : Rel a -> Rel a -> Rel a
Or p q = \i, j => Either (p i j) (q i j)

public export
0 And : Rel a -> Rel a -> Rel a
And p q = \i, j => (p i j, q i j)

public export
0 Not : Rel a -> Rel a
Not p = \i, j => Not (p i j)

public export
0 Const : Type -> Rel a
Const p = \i, j => p
