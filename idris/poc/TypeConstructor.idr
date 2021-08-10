import Data.List.Quantifiers

import Data.Vect

%default total

GFun : (arrow : a -> b -> b) -> List a -> b -> b
GFun arrow as r = foldr arrow r as

Fun : List Type -> Type -> Type
Fun = GFun (\a, b => a -> b)

Id : Type -> Type
Id = id

0 ForallC : (class : (a : Type) -> a -> Type) ->
            (as : List Type) -> (All Id as -> Type) -> Type
ForallC class [] k = k []
ForallC class (a :: as) k = {0 v : a} -> class a v => ForallC class as (k . (v ::))

Auto : List Type -> Type -> Type
Auto = GFun (\a, b => a => b)

curry : {as : List Type} -> (All Id as -> r) -> Fun as r
curry {as = []} f = f []
curry {as = a :: as} f = \ a => curry (f . (a ::))

uncurry : {as : List Type} -> Fun as r -> (All Id as -> r)
uncurry {as = []} f _ = f
uncurry {as = a :: as} f (v :: vs) = uncurry (f v) vs

TypeConstructor : List Type -> Type
TypeConstructor ix = Fun ix Type

OnType : (Type -> Type) -> (a : Type) -> a -> Type
OnType f Type v = f v
OnType f _ v = ()

0 MakeConstraint : (class : (a : Type) -> a -> Type) -> (ix : List Type) -> TypeConstructor ix -> Type
MakeConstraint class ix k = ForallC class ix $ \ xs => class _ (uncurry k xs)

FromConstraint : (ix : List Type) -> TypeConstructor ix ->
                 List ((ix : List Type) -> TypeConstructor ix -> Type) -> Type
FromConstraint ix k cs = GFun pair cs () where

  pair : ((ix : List Type) -> TypeConstructor ix -> Type) -> Type -> Type
  pair f acc = (f ix k, acc)

ListConstr : List (arity : List Type
                ** con : TypeConstructor arity
                ** FromConstraint arity con [ MakeConstraint (OnType Show)
                                            , MakeConstraint (OnType Eq)
                                            ])
ListConstr = [([] ** Nat ** %search)
             ,([Type] ** Maybe ** %search)
             ,([Type,Type] ** Either ** %search)
             ,([Nat,Type] ** Vect ** %search)
             ]
