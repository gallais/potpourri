module Free.Monad

import Free.Common

%default total

data Free : Pred Type -> Pred Type
FCont : Pred Type -> Rel Type
BCont : Pred Type -> Rel Type

data Free : Pred Type -> Pred Type where
  Pure : a -> Free m a
  Lift : m a -> Free m a
  Bind : Free m a -> BCont m a b -> Free m b

FCont m = Fwd (Kleisli (Free m))
BCont m = Bwd (Kleisli (Free m))

bind : Free m a -> (a -> Free m b) -> Free m b
bind (Pure a)     f = f a
bind (Lift m)     f = Bind (Lift m) (BNil :< f)
bind (Bind act k) f = Bind act (k :< f)

Functor (Free m) where
  map f t = bind t (Pure . f)

Applicative (Free m) where
  pure = Pure
  fs <*> xs = bind fs $ \ f => map (f $) xs

Monad (Free m) where
  (>>=) = bind

fold : (alg : {0 a : Type} -> m a -> a) ->
       (Free m a -> a)
fold alg t = freeK t FNil where

  cont : i -> FCont m i j -> j
  freeK : Free m i -> FCont m i j -> j

  cont i FNil = i
  cont i (f :> fs) = assert_total $ freeK (f i) fs

  freeK (Pure a)    k = cont a k
  freeK (Lift m)    k = cont (alg m) k
  freeK (Bind m fs) k = freeK m (fs <>> k)

homo : Monad n =>
       (f : {0 a : Type} -> m a -> n a) ->
       (Free m a -> n a)
homo f t = freeK t FNil where

  cont  : i -> FCont m i j -> n j
  freeK : Free m i -> FCont m i j -> n j

  cont i FNil      = pure i
  cont i (f :> fs) = assert_total $ freeK (f i) fs

  freeK (Pure a)    k = cont a k
  freeK (Lift m)    k = f m >>= \ x => cont x k
  freeK (Bind m fs) k = freeK m (fs <>> k)
