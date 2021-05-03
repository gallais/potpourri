module Free

%default total

Pred : Type -> Type
Pred a = a -> Type

Rel : Type -> Type
Rel a = a -> a -> Type

infixr 5 <|
data Fwd : Rel a -> Rel a where
  FNil : Fwd r i i
  (<|) : {0 r : Rel a} -> r i j -> Fwd r j k -> Fwd r i k

infixl 5 |>
data Bwd : Rel a -> Rel a where
  BNil : Bwd r i i
  (|>) : {0 r : Rel a} -> Bwd r i j -> r j k -> Bwd r i k

infixr 3 ><<
(><<) : Bwd r i j -> Fwd r j k -> Fwd r i k
BNil ><< gs = gs
(fs |> f) ><< gs = fs ><< (f <| gs)

reverse : Bwd r i j -> Fwd r i j
reverse fs = fs ><< FNil

Kleisli : Pred Type -> Rel Type
Kleisli m a b = a -> m b

data Free : Pred Type -> Pred Type
FCont : Pred Type -> Rel Type
BCont : Pred Type -> Rel Type

data Free : Pred Type -> Pred Type where
  Pure : a -> Free m a
  Bind : Free m a -> BCont m a b -> Free m b

FCont m = Fwd (Kleisli (Free m))
BCont m = Bwd (Kleisli (Free m))

Functor (Free m) where
  map f (Pure x) = Pure (f x)
  map f (Bind m fs) = Bind m (fs |> (Pure . f))

fold : (alg : {0 a : Type} -> m a -> a) ->
       (Free m a -> a)
fold alg t = freeK t FNil where

  cont : i -> FCont m i j -> j
  freeK : Free m i -> FCont m i j -> j

  cont i FNil = i
  cont i (f <| fs) = freeK (f i) fs

  freeK (Pure a) k = assert_total (cont a k)
  freeK (Bind m fs) k = freeK m (fs ><< k)
