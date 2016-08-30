{-# OPTIONS -Wall                  #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE PolyKinds             #-}

module Scopes where

import Utils
import Control.Newtype
import Data.Functor.Classes

-------------------------------------------------------------
-- BASIC SCOPE
-------------------------------------------------------------

newtype Scope (t :: * -> *) (a :: *) =
  Scope { runScope  :: t (Maybe a) }

instance Newtype (Scope t a) (t (Maybe a)) where
  pack   = Scope
  unpack = runScope

scope :: Scope ~~> Scope
scope = over Scope

instance Functor t => Functor (Scope t) where
  fmap f = over Scope (fmap (fmap f))

instance Show1 t => Show1 (Scope t) where
  showsPrec1 i (Scope t) = showString "Scope { runScope = "
                         . showsPrec1 i t
                         . showString " }"
instance (Show a, Show1 t) => Show (Scope t a) where showsPrec = showsPrec1

-------------------------------------------------------------
-- KRIPKE FUNCTION SPACE
-------------------------------------------------------------

newtype Kripke (e :: * -> *) (v :: * -> *) (a :: *) =
  Kripke { runKripke :: forall b. (a -> b) -> e b -> v b }

kripke :: Kripke e ~~> Kripke e
kripke f k = Kripke $ \ i e -> f $ runKripke k i e

instance Functor (Kripke e v) where
  fmap f e = Kripke $ \ i -> runKripke e (i . f)

abstract' :: (forall a. a -> e a) -> forall a. Kripke e v a -> v (Maybe a)
abstract' var k = runKripke k Just (var Nothing)

abstract :: (forall a. a -> e a) -> Kripke e (Const v r) ~> Scope v
abstract var = Scope . runConst . abstract' var

fixpoint :: Kripke v v ~> v
fixpoint kp = runKripke kp id (fixpoint kp)

