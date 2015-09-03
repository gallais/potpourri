{-# OPTIONS  -Wall #-}

module Equality where

import Data.Foldable as Fold
import Data.Sequence as Seq

import Context
import NormalForms           as NF
import Semantics
import qualified Language    as TM
import qualified FancyDomain as FD
import Data.Monoid

etaLam :: Ne g -> Nf g
etaLam (Cut v sp) = Bnd Lam $ Emb $ Cut (S v) $ NF.renamingSpine S sp <> w
  where w = Spine $ singleton $ App $ NF.var Z

eqEta :: Nf g -> Ne g -> Bool
eqEta t@(Bnd Lam _) u = eqNf t $ etaLam u
eqEta _             _ = False

eqNf :: Nf g -> Nf g -> Bool
-- normal forms
eqNf Set            Set            = True
eqNf Nat            Nat            = True
eqNf Zro            Zro            = True
eqNf (Suc m)        (Suc n)        = eqNf m n
eqNf (Bnd (Pi s) t) (Bnd (Pi u) v) = eqNf s u && eqNf t v
eqNf (Bnd Lam t)    (Bnd Lam u)    = eqNf t u
-- neutral forms
eqNf (Emb t)        (Emb u)        = eqNe t u
eqNf t              (Emb u)        = eqEta t u
eqNf (Emb t)        u              = eqEta u t
eqNf _              _              = False

eqNe :: Ne g -> Ne g -> Bool
eqNe (Cut a sp) (Cut b sq) = a == b && eqSpine sp sq
eqNe _          _          = False

eqSpine :: Spine g -> Spine g -> Bool
eqSpine (Spine sp) (Spine sq) =
  Seq.length sp == Seq.length sq
  && Fold.and (Seq.zipWith eqElim sp sq)

eqElim :: Elim g -> Elim g -> Bool
eqElim (App t)     (App u)     = eqNf t u
eqElim (Rec _ z s) (Rec _ y r) = eqNf z y && eqNf s r
eqElim _           _           = False

instance SContextI g => Eq (TM.Check g) where
  t == u = FD.normCheck t `eqNf` FD.normCheck u

instance SContextI g => Eq (TM.Infer g) where
  t == u = FD.normInfer t `eqNf` FD.normInfer u
