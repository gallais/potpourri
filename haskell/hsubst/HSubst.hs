module HSubst where

import Data.Void
import Data.Bifunctor
import Language
import Context

--------------------
--- Hereditary Substitution
--------------------

-- Hereditary Substitution is mostly functor-preserving
-- (except for `Ne`utral terms which are turned into
-- Normal ones) so we introduce this type alias.
type HSubst f a b c d =
  Subst a b c d -> Renaming a b c d -> f a b -> f c d

-- Now we can give a (rather) compact type to the combinator
-- lifting hereditary substitution to scopes
hSubstScopeDa :: (Eq a, Eq b, Eq c, Eq d) =>
  HSubst f (Maybe a) b (Maybe c) d -> HSubst (ScopeDa f) a b c d
hSubstScopeDa hS vu ren (ScopeDa sc) = ScopeDa $ hS vu' ren' sc
  where vu'  = wkSubstDa vu
        ren' = KeepItDa ren

hSubstScopeTm :: (Eq a, Eq b, Eq c, Eq d) =>
  HSubst f a (Maybe b) c (Maybe d) -> HSubst (ScopeTm f) a b c d
hSubstScopeTm hS vu ren (ScopeTm sc) = ScopeTm $ hS vu' ren' sc
  where vu'  = wkSubstTm vu
        ren' = KeepItTm ren

hSubstTy :: (Eq a, Eq b, Eq c, Eq d) => HSubst (Ty Nf) a b c d
hSubstTy _ _   TySet       = TySet
hSubstTy _ _   TyDat       = TyDat
hSubstTy _ _   TyZro       = TyZro
hSubstTy _ _   TyOne       = TyOne
hSubstTy _ _   TyTwo       = TyTwo
hSubstTy vu ren (TySig s t) = TySig s' t'
  where s' = hSubstTy vu ren s
        t' = hSubstScopeTm hSubstTy vu ren t
hSubstTy vu ren (TyAbs s t) = TyAbs s' t'
  where s' = hSubstTy vu ren s
        t' = hSubstScopeTm hSubstTy vu ren t
hSubstTy vu ren (TyRec d)   = TyRec $ hSubstScopeDa hSubstTy vu ren d
hSubstTy vu ren (TyElt t)   = TyElt $ hSubstNf vu ren t

hSubstNf :: (Eq a, Eq b, Eq c, Eq d) => HSubst Nf a b c d
hSubstNf vu ren (NfAbs b)   = NfAbs $ hSubstScopeTm hSubstNf vu ren b
hSubstNf vu ren (NfNeu ne)  = hSubstNe vu ren ne
hSubstNf vu ren (NfTyp ty)  = NfTyp $ hSubstTy vu ren ty
hSubstNf vu ren (NfInM t)   = NfInM $ hSubstNf vu ren t
hSubstNf vu ren (NfRec w)   = hSubstRec vu ren w
hSubstNf _ _    NfOne       = NfOne
hSubstNf _ _    NfTru       = NfTru
hSubstNf _ _    NfFls       = NfFls
hSubstNf vu ren (NfSig a b) = NfSig a' b'
  where a' = hSubstNf vu ren a
        b' = hSubstNf vu ren b

hSubstNe :: (Eq a, Eq b, Eq c, Eq d) =>
  Subst a b c d -> Renaming a b c d -> Ne a b -> Nf c d
hSubstNe wu ren (Ne v sp) = v' `hApp` sp'
  where v'  = hSubstVar wu ren v
        sp' = hSubstSp  wu ren sp

hSubstSp :: (Eq a, Eq b, Eq c, Eq d) => HSubst (Sp Nf) a b c d
hSubstSp vu ren (Sp sp) = Sp $ fmap (hSubstElim vu ren) sp

hSubstElim :: (Eq a, Eq b, Eq c, Eq d) => HSubst (Elim Nf) a b c d
hSubstElim vu ren (ElimApp t)      = ElimApp $ hSubstNf vu ren t
hSubstElim _ _    ElimPr1          = ElimPr1
hSubstElim _ _    ElimPr2          = ElimPr2
hSubstElim vu ren (ElimBot ty)     = ElimBot $ hSubstTy vu ren ty
hSubstElim vu ren (ElimTwo ty t f) = ElimTwo ty' (hNf t) (hNf f)
  where hNf = hSubstNf vu ren
        ty' = hSubstTy vu ren ty
hSubstElim vu ren (ElimRec ty alg) = ElimRec ty' $ hNf alg
  where ty' = hSubstTy vu ren ty
        hNf = hSubstNf vu ren

hSubstRec :: (Eq a, Eq b, Eq c, Eq d) =>
  Subst a b c d -> Renaming a b c d -> a -> Nf c d
hSubstRec (SubstTm v u) ren w = NfRec $ renameDa ren w
hSubstRec (SubstDa v u) ren w
  | v == w    = NfTyp u
  | otherwise = NfRec $ renameDa ren w

hSubstVar :: (Eq a, Eq b, Eq c, Eq d) =>
  Subst a b c d -> Renaming a b c d -> b -> Nf c d
hSubstVar (SubstDa v u) ren w = varNf $ renameTm ren w
hSubstVar (SubstTm v u) ren w
  | v == w    = u
  | otherwise = varNf $ renameTm ren w

hSubstTm :: (Eq a, Eq b) => ScopeTm Nf a b -> Nf a b -> Nf a b
hSubstTm b u = hSubstNf (SubstTm Nothing u) DropItTm $ outScopeTm b

hSubstDa :: (Eq a, Eq b) =>
            ScopeDa (Ty Nf) a b -> Ty Nf a b -> Ty Nf a b
hSubstDa b u = hSubstTy (SubstDa Nothing u) DropItDa $ outScopeDa b

appNe :: Ne a b -> Nf a b -> Ne a b
appNe ne = elimNe ne . ElimApp

appNf :: (Eq a, Eq b) => Nf a b -> Nf a b -> Nf a b
appNf (NfAbs b) u = hSubstTm b u

appTy :: (Eq a, Eq b) => Ty Nf a b -> Nf a b -> Ty Nf a b
appTy (TyAbs _ b) u =
  hSubstTy (SubstTm Nothing u) DropItTm $ outScopeTm b

funExt :: (Eq a, Eq b) =>
  ScopeDa (Ty Nf) a b -> Ty Nf a b -> Ty Nf a b
funExt d x = hSubstTy (SubstDa Nothing x) DropItDa $ outScopeDa d

elimNe :: Ne a b -> Elim Nf a b -> Ne a b
elimNe (Ne v (Sp sp)) elim = Ne v $ Sp $ sp ++ [elim]

proj1 :: Nf a b -> Nf a b
proj1 (NfSig a _) = a
proj1 (NfNeu ne)  = NfNeu $ elimNe ne ElimPr1

proj2 :: Nf a b -> Nf a b
proj2 (NfSig _ b) = b
proj2 (NfNeu ne)  = NfNeu $ elimNe ne ElimPr2

ifTE :: Ty Nf a b -> Nf a b -> Nf a b -> Nf a b -> Nf a b
ifTE _  NfTru      t _ = t
ifTE _  NfFls      _ f = f
ifTE ty (NfNeu ne) t f = NfNeu $ elimNe ne (ElimTwo ty t f)

elimNf :: (Eq a, Eq b) => Nf a b -> Elim Nf a b -> Nf a b
elimNf nf (ElimApp u)      = nf `appNf` u
elimNf nf ElimPr1          = proj1 nf
elimNf nf ElimPr2          = proj2 nf
elimNf nf (ElimTwo ty t f) = ifTE ty nf t f

hApp :: (Eq a, Eq b) => Nf a b -> Sp Nf a b -> Nf a b
hApp nf (Sp sp) = foldl elimNf nf sp
