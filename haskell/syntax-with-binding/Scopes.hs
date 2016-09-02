{-# OPTIONS -Wall                  #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE UndecidableInstances  #-}

module Scopes where

import Utils hiding (Compose)
import Control.Newtype
import Data.Functor.Compose
import Data.Functor.Classes

-------------------------------------------------------------
-- VAR LIKE
-------------------------------------------------------------

class VarLike (j :: i -> *) where
  type Next j :: i -> i
  var0    :: j (Next j n)
  weak    :: forall n. j n -> j (Next j n)
  inspect :: a -> (j n -> a) -> j (Next j n) -> a

instance VarLike Variable where
  type Next Variable = Maybe
  var0 = Variable Nothing
  weak = fmap Just
  inspect z s = maybe z s . sequenceA

instance VarLike Fin where
  type Next Fin = 'Succ
  var0 = Z
  weak = S
  inspect z s k = case k of
    Z    -> z
    S k' -> s k'

newtype DeBruijn (n :: Natural) = DeBruijn { runDeBruijn :: Integer }

instance Newtype (DeBruijn n) Integer where
  pack = DeBruijn
  unpack = runDeBruijn

instance VarLike DeBruijn where
  type Next DeBruijn = 'Succ
  var0 = DeBruijn 0
  weak = over DeBruijn (1+)
  inspect z s (DeBruijn k) = case k of
    0 -> z
    _ -> s $ DeBruijn $ k - 1

-------------------------------------------------------------
-- BASIC SCOPE
-------------------------------------------------------------

newtype Scope (j :: i -> *) (t :: i -> *) (a :: i) =
  Scope { runScope  :: t (Next j a) }

type Scope' = Scope Variable

instance (t' ~ t (Next j a)) => Newtype (Scope j t a) t' where
  pack   = Scope
  unpack = runScope

scope :: Scope j ~~> Scope j
scope = over Scope

instance (Functor (Next j), Functor t) => Functor (Scope j t) where
  fmap f = over Scope (fmap (fmap f))

instance (Show1 (Next j), Show1 t, Functor t) => Show1 (Scope j t) where
  showsPrec1 i (Scope t) = showString "Scope { runScope = "
                         . showsPrec1 i (Compose t)
                         . showString " }"
instance (Show a, Show1 (Next j), Show1 t, Functor t) => Show (Scope j t a) where showsPrec = showsPrec1

-------------------------------------------------------------
-- KRIPKE FUNCTION SPACE
-------------------------------------------------------------

newtype Kripke (j :: i -> *) (e :: i -> *) (v :: i -> *) (a :: i) =
  Kripke { runKripke :: forall b. (j a -> j b) -> e b -> v b }

type Kripke' = Kripke Variable

kripke :: Kripke j e ~~> Kripke j e
kripke f k = Kripke $ \ i e -> f $ runKripke k i e

instance Functor j => Functor (Kripke j e v) where
  fmap f e = Kripke $ \ i -> runKripke e (i . fmap f)

instance HigherFunctor j (Kripke j e v) where
  hfmap f e = Kripke $ runKripke e . (. f)

abstract :: VarLike j => (j ~> e) -> Kripke j e v ~> Scope j v
abstract var k = Scope $ runKripke k weak (var var0)

abstract' :: VarLike j => (j ~> e) -> Kripke j e (Const v r) ~> Scope j v
abstract' var = scope runConst . abstract var

fixpoint :: Kripke j v v ~> v
fixpoint kp = runKripke kp id (fixpoint kp)

fixpoint' :: v ~> v -> Kripke j v v ~> v
fixpoint' f kp = runKripke kp id (f $ fixpoint' f kp)
