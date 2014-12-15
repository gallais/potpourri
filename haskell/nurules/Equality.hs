{-# OPTIONS  -Wall #-}

module Equality where

import Context
import NormalForms
import qualified Language    as TM
import qualified FancyDomain as FD


etaLam :: Ne a -> Nf a
etaLam (Var a)    = Bnd Lam $ Emb $ Cut (Just a) [ App (Emb $ Var Nothing) ]
etaLam (Cut a sp) = Bnd Lam $ Emb $ Cut (Just a) $ fmap (fmap Just) sp ++ [ App (Emb $ Var Nothing) ]

eqEta :: Eq a => Nf a -> Ne a -> Bool
eqEta t@(Bnd Lam _) u = eqNf t $ etaLam u
eqEta _             _ = False

eqNf :: Eq a => Nf a -> Nf a -> Bool
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

eqNe :: Eq a => Ne a -> Ne a -> Bool
eqNe (Var a)    (Var b)    = a == b
eqNe (Cut a sp) (Cut b sq) = a == b && eqSpine sp sq
eqNe _          _          = False

eqSpine :: Eq a => Spine a -> Spine a -> Bool
eqSpine sp sq = and $ zipWith eqElim sp sq

eqElim :: Eq a => Elim a -> Elim a -> Bool
eqElim (App t)     (App u)     = eqNf t u
eqElim (Rec _ z s) (Rec _ y r) = eqNf z y && eqNf s r
eqElim _           _           = False

instance (Eq a, ValidContext a) => Eq (TM.Check a) where
  t == u = FD.normCheck t `eqNf` FD.normCheck u

instance (Eq a, ValidContext a) => Eq (TM.Infer a) where
  t == u = FD.normInfer t `eqNf` FD.normInfer u
