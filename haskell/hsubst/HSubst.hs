{-# LANGUAGE RankNTypes #-}

module HSubst where

import Language
import Context

--------------------
--- Hereditary Substitution
--------------------

-- Hereditary Substitution is mostly functor-preserving
-- (except for `Ne`utral terms which are turned into
-- Normal ones) so we introduce this type alias.
type HSubst f a b = a -> Nf b -> Renaming a b -> f a -> f b

-- Now we can give a (rather) compact type to the combinator
-- lifting hereditary substitution to scopes
hSubstScope :: (Eq a, Eq b) =>
  HSubst f (Maybe a) (Maybe b) -> HSubst (Scope f) a b
hSubstScope hS v u ren (Scope sc) = Scope $ hS v' u' ren' sc
  where v'   = Just v
        u'   = wkNf u
        ren' = KeepIt ren

-- And provide the required instances
hSubstScopeDa :: (Eq a, Eq b) => HSubst (Scope (Da Nf)) a b
hSubstScopeDa = hSubstScope hSubstDa
hSubstScopeTy :: (Eq a, Eq b) => HSubst (Scope (Ty Nf)) a b
hSubstScopeTy = hSubstScope hSubstTy
hSubstScopeNf :: (Eq a, Eq b) => HSubst (Scope Nf) a b
hSubstScopeNf = hSubstScope hSubstNf

hSubstDa :: (Eq a, Eq b) => HSubst (Da Nf) a b
hSubstDa _ _ _   DaVar       = DaVar
hSubstDa v u ren (DaCst ty)  = DaCst $ hSubstTy v u ren ty
hSubstDa v u ren (DaSig a b) = DaSig a' b'
  where
    a' = hSubstTy v u ren a
    b' = hSubstScopeDa v u ren b
hSubstDa v u ren (DaAbs a b) = DaAbs a' b'
  where
    a' = hSubstTy v u ren a
    b' = hSubstScopeDa v u ren b

hSubstTy :: (Eq a, Eq b) => HSubst (Ty Nf) a b
hSubstTy _ _ _   TySet       = TySet
hSubstTy _ _ _   TyZro       = TyZro
hSubstTy _ _ _   TyOne       = TyOne
hSubstTy _ _ _   TyTwo       = TyTwo
hSubstTy v u ren (TySig s t) = TySig s' t'
  where s' = hSubstTy      v u ren s
        t' = hSubstScopeTy v u ren t
hSubstTy v u ren (TyAbs s t) = TyAbs s' t'
  where s' = hSubstTy      v u ren s
        t' = hSubstScopeTy v u ren t
hSubstTy v u ren (TyRec d)   = TyRec $ hSubstDa v u ren d
hSubstTy v u ren (TyElt t)   = TyElt $ hSubstNf v u ren t

hSubstNf :: (Eq a, Eq b) => HSubst Nf a b
hSubstNf v u ren (NfAbs b)   = NfAbs $ hSubstScopeNf v u ren b
hSubstNf v u ren (NfNeu ne)  = hSubstNe v u ren ne
hSubstNf v u ren (NfTyp ty)  = NfTyp $ hSubstTy v u ren ty
hSubstNf v u ren (NfInM t)   = NfInM $ hSubstNf v u ren t
hSubstNf _ _ _   NfOne       = NfOne
hSubstNf _ _ _   NfTru       = NfTru
hSubstNf _ _ _   NfFls       = NfFls
hSubstNf v u ren (NfSig a b) = NfSig a' b'
  where a' = hSubstNf v u ren a
        b' = hSubstNf v u ren b

hSubstNe :: (Eq a, Eq b) =>
            a -> Nf b -> Renaming a b -> Ne a -> Nf b
hSubstNe w u ren (Ne v sp) = v' `hApp` sp'
  where v'  = hSubstVar w u ren v
        sp' = hSubstSp  w u ren sp

hSubstSp :: (Eq a, Eq b) => HSubst (Sp Nf) a b
hSubstSp v u ren (Sp sp) = Sp $ fmap (hSubstElim v u ren) sp

hSubstElim :: (Eq a, Eq b) => HSubst (Elim Nf) a b
hSubstElim v u ren (ElimApp t)      = ElimApp $ hSubstNf v u ren t
hSubstElim _ _ _   ElimPr1          = ElimPr1
hSubstElim _ _ _   ElimPr2          = ElimPr2
hSubstElim v u ren (ElimBot ty)     = ElimBot $ hSubstTy v u ren ty
hSubstElim v u ren (ElimTwo ty t f) = ElimTwo ty' (hNf t) (hNf f)
  where hNf = hSubstNf v u ren
        ty' = hSubstTy v u ren ty
hSubstElim v u ren (ElimRec ty alg) = ElimRec ty' $ hNf alg
  where ty' = hSubstTy v u ren ty
        hNf = hSubstNf v u ren


hSubstVar :: (Eq a, Eq b) => a -> Nf b -> Renaming a b -> a -> Nf b
hSubstVar v u ren w | v == w    = u
                    | otherwise = varNf $ rename ren w

hSubst :: Eq a => Scope Nf a -> Nf a -> Nf a
hSubst b u = hSubstNf Nothing u DropIt $ outScope b

appNe :: Ne a -> Nf a -> Ne a
appNe ne = elimNe ne . ElimApp

appNf :: Eq a => Nf a -> Nf a -> Nf a
appNf (NfAbs b) u = hSubst b u

appTy :: Eq a => Ty Nf a -> Nf a -> Ty Nf a
appTy (TyAbs _ b) u = hSubstTy Nothing u DropIt $ outScope b

elimNe :: Ne a -> Elim Nf a -> Ne a
elimNe (Ne v (Sp sp)) elim = Ne v $ Sp $ sp ++ [elim]

proj1 :: Nf a -> Nf a
proj1 (NfSig a _) = a
proj1 (NfNeu ne)  = NfNeu $ elimNe ne ElimPr1

proj2 :: Nf a -> Nf a
proj2 (NfSig _ b) = b
proj2 (NfNeu ne)  = NfNeu $ elimNe ne ElimPr2

ifTE :: Ty Nf a -> Nf a -> Nf a -> Nf a -> Nf a
ifTE _  NfTru      t _ = t
ifTE _  NfFls      _ f = f
ifTE ty (NfNeu ne) t f = NfNeu $ elimNe ne (ElimTwo ty t f)

elimNf :: Eq a => Nf a -> Elim Nf a -> Nf a
elimNf nf (ElimApp u)      = nf `appNf` u
elimNf nf ElimPr1          = proj1 nf
elimNf nf ElimPr2          = proj2 nf
elimNf nf (ElimTwo ty t f) = ifTE ty nf t f

hApp :: Eq a => Nf a -> Sp Nf a -> Nf a
hApp nf (Sp sp) = foldl elimNf nf sp
