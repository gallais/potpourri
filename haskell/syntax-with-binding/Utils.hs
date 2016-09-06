{-# OPTIONS -Wall                  #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE EmptyCase             #-}

module Utils where

import Data.Functor.Classes
import Control.Newtype

type (~>) (x :: k -> *) y = forall a. x a -> y a
type (~~>) (f :: (k -> *) -> (l -> *)) g = forall x y. x ~> y -> f x ~> g y

-------------------------------------------------------------
-- PAIRS
-------------------------------------------------------------

newtype Pair x a = Pair { runPair :: (x a, x a) }

pair :: (x a -> x' a') -> Pair x a -> Pair x' a'
pair f (Pair (t, u)) = Pair (f t, f u)

first :: Pair x ~> x
first (Pair (l, _)) = l

second :: Pair x ~> x
second (Pair (_, r)) = r

instance Functor x => Functor (Pair x) where
  fmap f (Pair (l, r)) = Pair (fmap f l, fmap f r)

instance HigherFunctor j x => HigherFunctor j (Pair x) where
  hfmap f (Pair (l, r)) = Pair (hfmap f l, hfmap f r)

-------------------------------------------------------------
-- CONST
-------------------------------------------------------------

newtype Const (v :: k -> *) (i :: l) (a :: k) = Const { runConst :: v a }
newtype CONST (a :: *) (i :: Natural) = CONST { runCONST :: a }

instance Newtype (CONST e i) e where
  pack = CONST
  unpack = runCONST

-------------------------------------------------------------
-- APPLY
-------------------------------------------------------------

newtype Apply (v :: k -> *) (a :: k) = Apply { runApply :: v a }

instance Newtype (Apply v a) (v a) where
  pack   = Apply
  unpack = runApply

-------------------------------------------------------------
-- COMPOSE
-------------------------------------------------------------

newtype Compose (g :: j -> *) (f :: i -> j) (a :: i) = Compose { runCompose :: g (f a) }

instance Newtype (Compose g f a) (g (f a)) where
  pack = Compose
  unpack = runCompose

-------------------------------------------------------------
-- VARIABLE
-------------------------------------------------------------

newtype Variable a = Variable { runVariable :: a }

instance Show1 Variable where showsPrec1 = showsPrec
deriving instance Show a => Show (Variable a)
deriving instance Functor Variable
deriving instance Foldable Variable
deriving instance Traversable Variable

instance Newtype (Variable a) a where
  pack   = Variable
  unpack = runVariable

-------------------------------------------------------------
-- NATURAL NUMBERS AND FIN
-------------------------------------------------------------

data Natural = Zero | Succ Natural
data Fin (n :: Natural) :: * where
  Z :: Fin ('Succ n)
  S :: Fin n -> Fin ('Succ n)

deriving instance Show (Fin n)

finZero :: Fin 'Zero -> forall a. a
finZero k = case k of {}


-------------------------------------------------------------
-- FUNCTOR BETWEEN FUNCTORS
-------------------------------------------------------------

class HigherFunctor (j :: i -> *) (e :: i -> *) where
  hfmap :: (j a -> j b) -> (e a -> e b)

instance HigherFunctor Variable Variable where
  hfmap = id

instance HigherFunctor Fin Fin where
  hfmap = id

instance HigherFunctor j (CONST e) where
  hfmap _ = CONST . runCONST

-------------------------------------------------------------
-- RELATIVE MONADS
-------------------------------------------------------------

class HigherFunctor j m => RelativeMonad (j :: i -> *) (m :: i -> *) where
  rreturn :: j ~> m
  rbind   :: m a -> (j a -> m b) -> m b
