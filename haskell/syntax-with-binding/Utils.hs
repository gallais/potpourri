{-# OPTIONS -Wall                  #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DeriveFunctor         #-}

module Utils where

import Control.Newtype

type (~>) (x :: k -> *) y = forall a. x a -> y a
type (~~>) (f :: (k -> *) -> (l -> *)) g = forall x y. x ~> y -> f x ~> g y

-------------------------------------------------------------
-- PAIRS
-------------------------------------------------------------

newtype Pair x a = Pair { runPair :: (x a, x a) }

pair :: (x a -> x' a') -> Pair x a -> Pair x' a'
pair f (Pair (t, u)) = Pair (f t, f u)

first :: Pair x a -> x a
first (Pair (l, _)) = l

second :: Pair x a -> x a
second (Pair (_, r)) = r

instance Functor x => Functor (Pair x) where
  fmap f (Pair (l, r)) = Pair (fmap f l, fmap f r)


-------------------------------------------------------------
-- CONST
-------------------------------------------------------------

newtype Const (v :: k -> *) (i :: l) (a :: k) = Const    { runConst :: v a }

-------------------------------------------------------------
-- APPLY
-------------------------------------------------------------

newtype Apply (v :: k -> *) (a :: k) = Apply { runApply :: v a }

instance Newtype (Apply v a) (v a) where
  pack   = Apply
  unpack = runApply


-------------------------------------------------------------
-- VARIABLE
-------------------------------------------------------------

newtype Variable a = Variable { runVar :: a }
deriving instance Functor Variable
