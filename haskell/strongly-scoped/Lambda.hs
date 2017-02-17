{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE IncoherentInstances    #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE RecordWildCards        #-}
{-# OPTIONS -Wall                   #-}

module Lambda where

import Prelude hiding (lookup)
import Data.Proxy

data Nat = Z | S Nat

data Var (m :: Nat) where
  Here  :: Var ('S m)
  There :: Var m -> Var ('S m)

data Tm (m :: Nat) where
  V :: Var m -> Tm m
  A :: Tm m -> Tm m -> Tm m
  L :: Tm ('S m) -> Tm m

data RTm a where
  RV :: a -> RTm a
  RA :: RTm a -> RTm a -> RTm a
  RL :: a -> RTm a -> RTm a

scopeCheck :: forall a. Eq a => RTm a -> Maybe (Tm 'Z)
scopeCheck = scopeCheck' (const Nothing)

scopeCheck' :: forall a. Eq a => forall m. (a -> Maybe (Var m)) -> RTm a -> Maybe (Tm m)
scopeCheck' rho e = case e of
  RV a   -> V <$> rho a
  RA f t -> A <$> scopeCheck' rho f <*> scopeCheck' rho t
  RL x b -> L <$> scopeCheck' (extend x rho) b

  where

    extend :: forall m. a -> (a -> Maybe (Var m)) -> (a -> Maybe (Var ('S m)))
    extend x rho y 
      | x == y    = return Here
      | otherwise = There <$> rho y

absurd :: Var 'Z -> a
absurd v = case v of {}

-- Environments are functions associating a well-scoped and
-- well-typed value to all the variables in range:

newtype Environment (e :: Nat -> *) (m :: Nat) (n :: Nat) =
  Pack { lookup :: Var m -> e n}

empty :: Environment e 'Z n
empty = Pack absurd

(#) :: forall e m n. Environment e m n -> e n -> Environment e ('S m) n
rho # val = Pack snoc where

  snoc :: Var ('S m) -> e n
  snoc Here      = val
  snoc (There v) = lookup rho v

-- Inclusions are a special type of environments


type Included = Environment Var

refl :: Included m m
refl = Pack id

step :: Included m n -> Included m ('S n)
step rho = Pack $ There . lookup rho

type family LT (m :: Nat) (n :: Nat) where
  LT m ('S n) = LE m n
  LT m n      = 'False

type family LE (m :: Nat) (n :: Nat) where
  LE m n = OR (EQ m n) (LT m n)

type family EQ x y where
  EQ x x = 'True
  EQ x y = 'False

type family OR (b :: Bool) (c :: Bool) where
  OR 'True c  = 'True
  OR b 'True  = 'True
  OR b 'False = b
  OR 'False c = c

class Extension (m :: Nat) (n :: Nat) (b :: Bool) where
  steps :: Proxy b -> Included m n

instance Extension m m b where
  steps _ = refl

instance Extension m n (LT m n) => Extension m ('S n) 'True where
  steps _ = step $ steps (Proxy :: Proxy (LT m n))

newtype FreshVar m =
  FreshVar { runFreshVar :: forall n. Extension ('S m) n (LT ('S m) n) => Var n }

class FreshVariable (v :: Nat -> *) where
  var :: forall m n. Extension ('S m) n (LT ('S m) n) => FreshVar m -> v n

instance FreshVariable Var where
  var = runFreshVar

instance FreshVariable Tm where
  var = V . runFreshVar

lam :: forall m. (FreshVar m -> Tm ('S m)) -> Tm m
lam b = L $ b $ FreshVar $ freshVar where

  freshVar :: forall n. Extension ('S m) n (LT ('S m) n) => Var n
  freshVar = lookup (steps (Proxy :: Proxy (LT ('S m) n))) (Here :: Var ('S m))

identity :: Tm m
identity = lam $ \ x -> var x

true :: Tm m
true = lam $ \ x ->
       lam $ \ _ ->
       var x

false :: Tm m
false = lam $ \ _ -> identity


