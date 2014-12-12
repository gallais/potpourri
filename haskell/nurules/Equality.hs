{-# OPTIONS  -Wall #-}

module Equality where

import Language

etaLam :: Infer a -> Check a
etaLam (Var a)    = Bnd Lam $ Emb $ Cut (Var $ Just a) [ App (Emb $ Var Nothing) ]
etaLam (Cut t sp) = Bnd Lam $ Emb $ Cut (fmap Just t) $ fmap (fmap Just) sp ++ [ App (Emb $ Var Nothing) ]

eqEta :: Eq a => Check a -> Infer a -> Bool
eqEta t@(Bnd Lam _) u = eqCheck t $ etaLam u
eqEta _             _ = False

eqCheck :: Eq a => Check a -> Check a -> Bool
-- normal forms
eqCheck Set            Set            = True
eqCheck Nat            Nat            = True
eqCheck Zro            Zro            = True
eqCheck (Suc m)        (Suc n)        = eqCheck m n
eqCheck (Bnd (Pi s) t) (Bnd (Pi u) v) = eqCheck s u && eqCheck t v
eqCheck (Bnd Lam t)    (Bnd Lam u)    = eqCheck t u
-- neutral forms
eqCheck (Emb t)        (Emb u)        = eqInfer t u
eqCheck t              (Emb u)        = eqEta t u
eqCheck (Emb t)        u              = eqEta u t


eqInfer :: Eq a => Infer a -> Infer a -> Bool
eqInfer (Var a)    (Var b)    = a == b
eqInfer (Cut t sp) (Cut u sq) = eqInfer t u && eqSpine sp sq
eqInfer (Ann t _)  (Ann u _)  = eqCheck t u

eqSpine :: Eq a => Spine a -> Spine a -> Bool
eqSpine sp sq = and $ zipWith eqElim sp sq

eqElim :: Eq a => Elim a -> Elim a -> Bool
eqElim (App t)     (App u)     = eqCheck t u
eqElim (Rec _ z s) (Rec _ y r) = eqCheck z y && eqCheck s r
