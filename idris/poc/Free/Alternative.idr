module Free.Alternative

import Data.List
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
  alternatives : List1 (Free m i)
  continuation : FCont m i j

(::) : (List (Free m i), FCont m i j) ->
       List (Alts m j) -> List (Alts m j)
([], _)        :: alts = alts
((m :: ms), k) :: alts = MkAlts (m ::: ms) k :: alts

fold : (alg : {0 a : Type} -> m a -> a) ->
       (Free m a -> Maybe a)
fold alg t = freeK t [] FNil where

  cont   : i -> List (Alts m j) -> FCont m i j -> Maybe j
  freeK : Free m i -> List (Alts m j) -> FCont m i j -> Maybe j
  first  : List (Alts m j) -> Maybe j

  cont i alts FNil = Just i
  cont i alts (f :> fs) = assert_total $ freeK (f i) alts fs

  freeK (Pure a)             alts k = cont a alts k
  freeK Fail                 alts k = first alts
  freeK (Lift m)             alts k = cont (alg m) alts k
  freeK (Bind (m ::: ms) fs) alts k
    = let k = fs <>> k in
      freeK m ((ms, k) :: alts) k

  first [] = Nothing
  first (MkAlts (m ::: ms) k :: alts)
    = assert_total $ freeK m ((ms, k) :: alts) k

homo : Monad n =>
       (f : {0 a : Type} -> m a -> n a) ->
       (Free m a -> n (Maybe a))
homo f t = freeK t [] FNil where

  cont   : i -> List (Alts m j) -> FCont m i j -> n (Maybe j)
  freeK  : Free m i -> List (Alts m j) -> FCont m i j -> n (Maybe j)
  first  : List (Alts m j) -> n (Maybe j)

  cont i alts FNil      = pure (Just i)
  cont i alts (f :> fs) = assert_total $ freeK (f i) alts fs

  freeK (Pure a)             alts k = cont a alts k
  freeK Fail                 alts k = first alts
  freeK (Lift m)             alts k = f m >>= \ x => cont x alts k
  freeK (Bind (m ::: ms) fs) alts k
    = let k = fs <>> k in
      freeK m ((ms,k) :: alts) k

  first [] = pure Nothing
  first (MkAlts (m ::: ms) k :: alts)
    = assert_total $ freeK m ((ms, k) :: alts) k

--------------------------------------------------------------
-- Example

data Eff : Type -> Type where
  Get      : Eff Nat
  PutStrLn : String -> Eff ()

prog : Free Eff ()
prog = sequence_ (replicate 3 printInput)
   <|> Lift (PutStrLn "Failed!")

  where

  printInput : Free Eff ()
  printInput = do
    n <- Lift Get
    if n == Z then Fail else Lift (PutStrLn (show n))

run : IO ()
run = ignore $ flip homo prog $ \case
  Get          => length <$> getLine
  (PutStrLn x) => putStrLn x
