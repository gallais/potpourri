module Union

import Data.DPair
import Decidable.Equality

%default total

public export
data AtIndex : Nat -> a -> List a -> Type where
  Z : AtIndex Z a (a :: as)
  S : AtIndex n a as -> AtIndex (S n) a (b :: as)

public export
Uninhabited (AtIndex n a []) where
  uninhabited Z impossible
  uninhabited (S _) impossible

public export
atIndexUnique : AtIndex k a as -> AtIndex k b as -> a === b
atIndexUnique Z Z = Refl
atIndexUnique (S p) (S q) = atIndexUnique p q

public export
data Union : (ts : List (Type -> Type)) -> Type -> Type where
  Element : (k : Nat) -> {auto 0 _ : AtIndex k t ts} -> t v -> Union ts v

public export
Uninhabited (Union [] v) where uninhabited (Element _ @{p} _) = void (uninhabited p)

public export
inj' : (k : Nat) -> {auto 0 _ : AtIndex k t ts} -> t v -> Union ts v
inj' = Element

public export
prj' : (k : Nat) -> {auto 0 _ : AtIndex k t ts} -> Union ts v -> Maybe (t v)
prj' k @{p} (Element k' @{q} t) with (decEq k  k')
  prj' k @{p} (Element k @{q} t) | Yes Refl = rewrite atIndexUnique p q in Just t
  prj' k (Element k' t) | No neq = Nothing

public export
interface FindElement (0 t : a) (0 ts : List a) where
  findElement : Subset Nat (\ k => AtIndex k t ts)

FindElement t (t :: ts) where
  findElement = Element 0 Z

FindElement t ts => FindElement t (u :: ts) where
  findElement = let (Element n prf) = findElement in
                Element (S n) (S prf)

public export
interface FindElement t ts => Member (0 t : Type -> Type) (0 ts : List (Type -> Type)) where
  inj : t v -> Union ts v
  inj = let (Element n p) = findElement in inj' n

  prj : Union ts v -> Maybe (t v)
  prj = let (Element n p) = findElement in prj' n

public export
decomp : Union (t :: ts) v -> Either (Union ts v) (t v)
decomp (Element 0     @{Z}   t) = Right t
decomp (Element (S n) @{S p} t) = Left (Element n t)

public export
decomp0 : Union [t] v -> t v
decomp0 elt = case decomp elt of
  Left t => absurd t
  Right t => t

public export
weaken : Union ts v -> Union (t :: ts) v
weaken (Element n t) = Element (S n) t
