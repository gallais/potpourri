{-# OPTIONS -Wall                  #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}

module Generic where

import Data.Functor.Classes
import Data.Proxy

import Utils
import Scopes

-------------------------------------------------------------
-- SYNTAX WITH BINDING
-------------------------------------------------------------

-- This is what I'd like to write:
-- kind Scoped  = * -> *
-- kind ScopedT = Scoped -> Scoped
-- kind Syntax  = ScopedT -> Scoped
-- kind SyntaxT = Syntax -> Syntax
-- class SyntaxWithBinding (syn :: SyntaxT) where

class SyntaxWithBinding
      (syn :: (((* -> *) -> (* -> *)) -> (* -> *))
           ->  ((* -> *) -> (* -> *)) -> (* -> *)) where
  reindex :: (scp  ~~> scp)
          -> (scp' ~~> scp')
          -- Reindexing properties
          -> (rec scp a -> rec' scp' a')
          -> (forall f. (forall b b'. (rec scp b -> rec' scp' b')
                                   -> f (rec scp) b -> f (rec' scp') b')
                     -> scp (f (rec scp)) a -> scp' (f (rec' scp')) a')
          -> syn rec scp a -> syn rec' scp' a'


-------------------------------------------------------------
-- FIXPOINT OF A SYNTAX TRANSFORMER
-------------------------------------------------------------

data Fix f (s :: (* -> *) -> (* -> *)) (a :: *) :: * where
   Var :: a             -> Fix f s a
   Fix :: f (Fix f) s a -> Fix f s a

instance Show1 (f (Fix f) s) => Show1 (Fix f s) where
  showsPrec1 i e = case e of
    Var v -> showString "Var " . showsPrec (1+i) v
    Fix t -> showString "Fix " . showsPrec1 (1+i) t
deriving instance (Show a, Show (f (Fix f) s a)) => Show (Fix f s a)

-------------------------------------------------------------
-- ALGEBRAS, EVALUATION AND FUNDAMENTAL LEMMA OF SYNTAXES
-------------------------------------------------------------

class Alg  t e v where
  alg  :: t (Const v) (Kripke e) a -> v a
  ret  :: Proxy t -> e ~> v

class Eval t e v where
  eval  :: (a -> e b) -> t a -> v b
  eval' :: Proxy e -> (a -> e b) -> t a -> v b
  eval' _ = eval


instance (Functor e, SyntaxWithBinding t, Alg t e v) => Eval (Fix t Scope) e v where
  eval = go where

    go :: forall a b. (a -> e b) -> Fix t Scope a -> v b
    go rho (Var a) = ret (Proxy :: Proxy t) $ rho a
    go rho (Fix t) = alg $ reindex scope
                                   kripke
                                   (Const . go rho)
                                   (\ g b -> Kripke $ \ i e ->
                                             g (Const . go (maybe e (fmap i . rho)))
                                             $ runScope b)
                                   t
-------------------------------------------------------------
-- RENAMING AND SUBSTITUTION
-------------------------------------------------------------

rename :: (SyntaxWithBinding t, Alg t Variable (Fix t Scope)) =>
          Fix t Scope a -> (a -> b) -> Fix t Scope b
rename = flip $ eval . (Variable .)

subst :: (SyntaxWithBinding t, Alg t (Fix t Scope) (Fix t Scope), Functor (Fix t Scope)) =>
         Fix t Scope a -> (a -> Fix t Scope b) -> Fix t Scope b
subst = flip eval

-------------------------------------------------------------
-- MODEL OF A SYNTAXT AND NORMALISATION BY EVALUTION
-------------------------------------------------------------

newtype Model f a = Model { runModel :: Fix f (Kripke (Model f)) a }

reflect :: a -> Model f a
reflect = Model . Var

reify :: forall f. SyntaxWithBinding f => Model f ~> Fix f Scope
reify = go . runModel where

  go :: Fix f (Kripke (Model f)) ~> Fix f Scope
  go (Var a) = Var a
  go (Fix f) = Fix $ reindex kripke scope go
                     (\ g -> Scope . g go . abstract' reflect)
                     f

norm ::
  forall t. SyntaxWithBinding t
         => Functor (Model t)
         => Alg t (Model t) (Model t)
         => Fix t Scope ~> Fix t Scope
norm = reify . eval' (Proxy :: Proxy (Model t)) reflect
