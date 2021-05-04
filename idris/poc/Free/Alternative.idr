module Free.Alternative

import Data.List1
import Free.Common

%default total

data Free : Pred Type -> Pred Type
FCont : Pred Type -> Rel Type
BCont : Pred Type -> Rel Type

data Free : Pred Type -> Pred Type where
  Pure : a -> Free m a
  Fail : Free m a
  Lift : m a -> Free m a
  Bind : List1 (Free m a) -> BCont m a b -> Free m b

FCont m = Fwd (Kleisli (Free m))
BCont m = Bwd (Kleisli (Free m))

bind : Free m a -> (a -> Free m b) -> Free m b
bind (Pure a)   f = f a
bind Fail       f = Fail
bind m@(Lift _) f = Bind (m ::: []) (BNil :< f)
bind (Bind m k) f = Bind m (k :< f)

Functor (Free m) where
  map f t = bind t (Pure . f)

Applicative (Free m) where
  pure = Pure
  fs <*> xs = bind fs $ \ f => map (f $) xs

Monad (Free m) where
  (>>=) = bind

Alternative (Free m) where
  empty = Fail
  Bind ms BNil <|> Bind ns BNil = Bind (ms ++ ns) BNil
  m <|> n = Bind (m ::: [n]) BNil

choice : List (Free m a) -> Free m a
choice [] = Fail
choice (t :: ts) = Bind (t ::: ts) BNil

record Alts (m : Pred Type) (j : Type) where
  constructor MkAlts
  {0 i : Type}
  alternatives : List (Free m i)
  continuation : FCont m i j

noAlts : Alts m i
noAlts = MkAlts {i} [] FNil

fold : (alg : {0 a : Type} -> m a -> a) ->
       (Free m a -> Maybe a)
fold alg t = freeK t FNil where

  cont   : i -> FCont m i j -> Maybe j
  freeK  : Free m i -> FCont m i j -> Maybe j
  freeKs : Free m i -> Alts m j -> FCont m i j -> Maybe j
  first  : Alts m j -> Maybe j

  cont i FNil = pure i
  cont i (f :> fs) = assert_total $ freeK (f i) fs

  freeK m k = freeKs m noAlts k

  freeKs (Pure a)             alts k = cont a k
  freeKs Fail                 alts k = first alts
  freeKs (Lift m)             alts k = cont (alg m) k
  freeKs (Bind (m ::: ms) fs) alts k
    = let k = fs <>> k in freeKs m (MkAlts ms k) k

  first (MkAlts [] _) = Nothing
  first (MkAlts (m :: ms) k)
    = assert_total $ freeKs m (MkAlts ms k) k

{-
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
-}
