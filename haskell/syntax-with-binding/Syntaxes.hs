{-# OPTIONS -Wall                  #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE PatternSynonyms       #-}

module Syntaxes where

import Data.Function
import Data.Functor.Classes
import Control.Newtype

import Utils
import Scopes
import Generic

-------------------------------------------------------------
-- UNTYPED LAMBDA CALCULUS
-------------------------------------------------------------

type Term = Fix TmF Scope

data TmF (r :: ((* -> *) -> (* -> *)) -> (* -> *))
         (s :: (* -> *) -> (* -> *))
         (a :: *)
         :: * where
  L :: s (r s) a      -> TmF r s a -- Lambda Abstraction
  A :: r s a -> r s a -> TmF r s a -- Application

instance SyntaxWithBinding TmF where
  reindex fs fs' r s e = case e of
    L b   -> L $ fs' runApply $ s (over Apply) $ fs Apply b
    A f t -> A (r f) (r t)

pattern TmL t   = Fix (L (Scope t))
pattern TmA f t = Fix (A f t)

-------------------------------------------------------------
-- UNTYPED LAMBDA CALCULUS WITH UNIT, SUMS, AND FIXPOINTS
-------------------------------------------------------------

type Case = Fix CsF Scope

data CsF (r :: ((* -> *) -> (* -> *)) -> (* -> *))
         (s :: (* -> *) -> (* -> *))
         (a :: *)
         :: * where
  LI :: r s a -> CsF r s a                     -- Left  Injection
  RI :: r s a -> CsF r s a                     -- Right Injection
  CA :: r s a -> s (Pair (r s)) a -> CsF r s a -- Case  Analysis
  FX :: s (r s) a -> CsF r s a                 -- Fixpoint Operator
  LA :: s (r s) a -> CsF r s a                 -- Lambda Abstraction
  AP :: Pair (r s) a -> CsF r s a              -- Application
  UN :: CsF r s a                              -- Unit

instance SyntaxWithBinding CsF where
  reindex fs fs' r s e = case e of
    LI t   -> LI $ r t
    RI t   -> RI $ r t
    CA c b -> CA (r c) $ s pair b
    FX f   -> FX $ fs' runApply $ s (over Apply) $ fs Apply f
    LA b   -> LA $ fs' runApply $ s (over Apply) $ fs Apply b
    AP p   -> AP $ pair r p
    UN     -> UN

pattern CsLI t   = Fix (LI t)
pattern CsRI t   = Fix (RI t)
pattern CsCA t b = Fix (CA t (Scope b))
pattern CsFX f   = Fix (FX (Scope f))
pattern CsLA f   = Fix (LA (Scope f))
pattern CsAP f t = Fix (AP (Pair (f, t)))
pattern CsUN     = Fix UN

($$) :: Case a -> Case a -> Case a
($$) f t = CsAP f t

-------------------------------------------------------------
-- ALGEBRAS FOR RENAMING
-------------------------------------------------------------

instance Alg TmF Variable Term where
  ret _ = Var . runVar
  alg e = case e of
    L b   -> TmL $ abstract' Variable $ kripke runConst b
    A f t -> (TmA `on` runConst) f t
instance Functor (Fix TmF Scope) where fmap = flip rename

instance Alg CsF Variable Case where
  ret _ = Var . runVar
  alg e = Fix $ case e of
    LI t    -> LI $ runConst t
    RI t    -> RI $ runConst t
    CA f kp -> CA (runConst f) $ Scope $ pair runConst $ abstract' Variable kp
    FX f    -> FX $ abstract Variable f
    LA b    -> FX $ abstract Variable b
    AP p    -> AP $ pair runConst p
    UN      -> UN
instance Functor (Fix CsF Scope) where fmap = flip rename

-------------------------------------------------------------
-- ALGEBRAS FOR SUBSTITUTION
-------------------------------------------------------------

instance Alg TmF Term Term where
  ret _ = id
  alg e = case e of
    L b   -> TmL $ abstract' Var $ kripke runConst b
    A f t -> (TmA `on` runConst) f t

instance Alg CsF Case Case where
  ret _ = id
  alg e = Fix $ case e of
    LI t    -> LI $ runConst t
    RI t    -> RI $ runConst t
    CA f kp -> CA (runConst f) $ Scope $ pair runConst $ runKripke kp Just (Var Nothing)
    FX kp   -> FX $ abstract Var kp
    LA b    -> LA $ abstract Var b
    AP p    -> AP $ pair runConst p
    UN      -> UN

-------------------------------------------------------------
-- ALGEBRAS FOR NORMALISATION BY EVALUATION
-------------------------------------------------------------

instance Alg TmF (Model TmF) (Model TmF) where
  ret _ = id
  alg e = case e of
    L b   -> Model $ Fix $ L $ kripke (runModel . runConst) b
    A f t -> case runModel (runConst t) of
      Fix (L b) -> Model $ runKripke b id (runConst t)
      _         -> Model $ Fix $ (A `on` runModel . runConst) f t

instance Alg CsF (Model CsF) (Model CsF) where
  ret _ = id
  alg e =
    let cleanup = runModel . runConst
    in case e of
    LI t    -> Model $ Fix $ LI $ cleanup t
    RI t    -> Model $ Fix $ RI $ cleanup t
    CA f kp -> case cleanup f of
      CsLI l -> runConst $ first  $ runKripke kp id $ Model l 
      CsRI r -> runConst $ second $ runKripke kp id $ Model r
      f'     -> Model $ Fix $ CA f' $ kripke (pair cleanup) kp
    FX kp   -> fixpoint $ kripke runConst kp
    LA b    -> Model $ Fix $ LA $ kripke cleanup b
    AP p    -> Model $ case cleanup (first p) of
      Fix (LA b) -> runKripke b id (runConst $ second p)
      _          -> Fix $ AP $ pair cleanup p    
    UN      -> Model $ Fix UN      

instance Functor (Fix TmF (Kripke (Model f))) where
  fmap f e = case e of
    Var a       -> Var (f a)
    Fix e' -> Fix $ case e' of
      L b   -> L $ fmap f b
      A t u -> (A `on` fmap f) t u
deriving instance Functor (Model TmF)

instance Functor (Fix CsF (Kripke (Model CsF))) where
  fmap f e = case e of
    Var a  -> Var $ f a
    Fix e' -> Fix $ case e' of
      LI t    -> LI $ fmap f t
      RI t    -> RI $ fmap f t
      CA t kp -> CA (fmap f t) $ fmap f kp
      FX kp   -> FX $ fmap f kp
      LA kp   -> LA $ fmap f kp
      AP p    -> AP $ fmap f p
      UN      -> UN
deriving instance Functor (Model CsF)


-------------------------------------------------------------
-- SHOW INSTANCES
-------------------------------------------------------------

instance (Show1 (r s), Show1 (s (r s))) => Show1 (TmF r s) where
  showsPrec1 i e = case e of
    L b   -> showString "L " . showsPrec1 (1+i) b
    A f t -> showsBinary1 "A" i f t

deriving instance (Show (r s a), Show (s (r s) a)) => Show (TmF r s a)


