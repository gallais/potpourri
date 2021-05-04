module Free.Common

%default total

public export
Pred : Type -> Type
Pred a = a -> Type

public export
Rel : Type -> Type
Rel a = a -> a -> Type

infixr 5 :>
public export
data Fwd : Rel a -> Rel a where
  FNil : Fwd r i i
  (:>) : {0 r : Rel a} -> r i j -> Fwd r j k -> Fwd r i k

infixl 5 :<
public export
data Bwd : Rel a -> Rel a where
  BNil : Bwd r i i
  (:<) : {0 r : Rel a} -> Bwd r i j -> r j k -> Bwd r i k

infixr 3 <>>
export
(<>>) : Bwd r i j -> Fwd r j k -> Fwd r i k
BNil <>> gs = gs
(fs :< f) <>> gs = fs <>> (f :> gs)

public export
Kleisli : Pred Type -> Rel Type
Kleisli m a b = a -> m b
