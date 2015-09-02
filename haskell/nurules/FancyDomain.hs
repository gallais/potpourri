{-# OPTIONS  -Wall          #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}

module FancyDomain where

import Data.Sequence as Seq

import Context
import qualified Language    as TM
import Semantics
import qualified NormalForms as NF

----------------------------------------------------
-- THE EVALUATION DOMAIN
-- We opt for a well-scoped by construction approach which lets us
-- avoid the back-and-forth motion bewteen de Bruijn levels / indices
-- typical of name generation-based approaches.
-- This is made possible by the typical Kripke structure of the BND
-- construct taking into account all possible future extensions of
-- the current scope.
----------------------------------------------------

data Dom (g :: Context) =
    NF (ActDom g)
  | NE (Var g) (Spine g)
  | BT

data Elim (g :: Context) =
    APP (Dom g)
  | REC (Dom g) (Dom g) (Dom g)

newtype Spine (g :: Context) = Spine { unSpine :: Seq (Elim g) }

data ActDom (g :: Context) =
    BND (Binder g) (forall d. Renaming g d -> Dom d -> Dom d)
  | SUC (Dom g)
  | ZRO
  | NAT
  | SET

data Binder (g :: Context) = LAM | PI (Dom g)

-- Renaming for the domain

weakDom :: Renaming g d -> Dom g -> Dom d
weakDom ren (NF ad)   = NF $ weakActDom ren ad
weakDom ren (NE v sp) = NE (ren v) $ weakSpine ren sp
weakDom _   BT        = BT

weakActDom :: Renaming g d -> ActDom g -> ActDom d
weakActDom ren (BND bd t) = BND (weakBinder ren bd) $ t . trans ren
weakActDom ren (SUC n)    = SUC $ weakDom ren n
weakActDom _   ZRO        = ZRO
weakActDom _   NAT        = NAT
weakActDom _   SET        = SET

weakBinder :: Renaming g d -> Binder g -> Binder d
weakBinder _   LAM    = LAM
weakBinder ren (PI a) = PI $ weakDom ren a

weakElim :: Renaming g d -> Elim g -> Elim d
weakElim ren (APP u)      = APP $ weakDom ren u
weakElim ren (REC ty s z) = REC (wk ty) (wk s) (wk z)
  where wk = weakDom ren

weakSpine :: Renaming g d -> Spine g -> Spine d
weakSpine ren = Spine . fmap (weakElim ren) . unSpine

----------------------------------------------------
-- EVALUATION
----------------------------------------------------

data BinderOrLet (g :: Context) = BINDER (Binder g) | LET (Dom g)

domCUT :: Dom g -> Spine g -> Dom g
domCUT (NE v sp)  sp' = NE v $ Spine $ unSpine sp >< unSpine sp'
domCUT nf@(NF ad) sp  =
  case viewl $ unSpine sp of
    EmptyL    -> nf
    el :< sp' -> actCUT ad el (Spine sp')
domCUT BT         _   = BT

actCUT :: ActDom g -> Elim g -> Spine g -> Dom g
actCUT ZRO       (REC _ _ z)   = domCUT z
actCUT (SUC n)   r@(REC _ s _) = domCUT $ domCUT s $ Spine sp
  where sp = fromList [ APP n , APP $ domCUT n $ Spine $ singleton r ]
actCUT (BND _ t) (APP el)      = domCUT (t refl el)
actCUT _ _ = const BT

normalisation :: Semantics Dom Dom BinderOrLet Dom Elim Spine
normalisation = Semantics
  { weak  = weakDom
  , embed = \ v -> NE v $ Spine empty
  , var   = id
  , cut   = domCUT
  , ann   = const
  , lam   = BINDER LAM
  , piT   = BINDER . PI
  , letx  = LET
  , bnd   = \ bdOrLet t -> case bdOrLet of
                             LET v     -> t refl v
                             BINDER bd -> NF $ BND bd t
  , zro   = NF ZRO
  , suc   = NF . SUC
  , emb   = id
  , nat   = NF NAT
  , set   = NF SET
  , app   = APP
  , rec   = REC
  , spine = Spine
  }

----------------------------------------------------
-- THE REIFICATION PROCESS
----------------------------------------------------

reflect :: Var g -> Dom g
reflect v = NE v $ Spine empty

reify :: Dom g -> NF.Nf g
reify (NF d)    = reifyAct d
reify (NE v sp) = NF.Emb $ NF.Cut v $ NF.Spine $ fmap reifyArg $ unSpine sp

reifyAct :: ActDom g -> NF.Nf g
reifyAct (BND bd t) = NF.Bnd (reifyBinder bd) $ reify $ t (top refl) $ reflect Z
reifyAct (SUC d)    = NF.Suc $ reify d
reifyAct ZRO        = NF.Zro
reifyAct NAT        = NF.Nat
reifyAct SET        = NF.Set

reifyBinder :: Binder g -> NF.Binder g
reifyBinder LAM    = NF.Lam
reifyBinder (PI a) = NF.Pi $ reify a

reifyArg :: Elim g -> NF.Elim g
reifyArg (APP t)      = NF.App $ reify t
reifyArg (REC ty z s) = NF.Rec (reify ty) (reify z) (reify s)

instance SContextI g => Show (Dom g) where
  show d = show $ reify d

normInfer :: TM.Infer a -> NF.Nf a
normInfer t = reify $ lemmaInfer normalisation t $ reflect

normCheck :: TM.Check a -> NF.Nf a
normCheck t = reify $ lemmaCheck normalisation t $ reflect
