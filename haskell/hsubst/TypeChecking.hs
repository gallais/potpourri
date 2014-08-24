module TypeChecking where

import Language
import Context
import HSubst

-------------------
-- Bidirectional Typechecking
-------------------

-- type-checking for Normal Forms

checkTy :: Eq a => Context a -> Ty Nf a -> ()
checkTy _ _ = ()

checkNf :: Eq a => Context a -> Ty Nf a -> Nf a -> ()
checkNf ga (TyElt (NfTyp ty)) te = checkNf ga ty te
checkNf ga (TyAbs s t) (NfAbs b) = checkNf (ga .~. s) t' b'
  where t' = outScope t
        b' = outScope b
checkNf ga TySet (NfTyp ty) = checkTy ga ty
checkNf ga (TyRec d) (NfInM r) = checkNf ga (funExt d (TyRec d)) r
checkNf _ TyOne NfOne = ()
checkNf _ TyTwo NfTru = ()
checkNf _ TyTwo NfFls = ()
checkNf ga (TySig s t) (NfSig a b) =
  case checkNf ga s a of
    () -> checkNf ga (TyAbs s t `appTy` a) b
checkNf ga ty (NfNeu ne)
  | ty == inferNe ga ne = ()

-- type-inference for Neutral Terms

inferNe :: Eq a => Context a -> Ne a -> Ty Nf a
inferNe ga (Ne v sp) = inferSp ga (ga `givesTypeTo` v, varNe v) sp

inferElim :: Eq a =>
  Context a -> (Ty Nf a, Ne a) -> Elim Nf a -> (Ty Nf a, Ne a)
inferElim ga (ty@(TyAbs s _), ne) (ElimApp nf) =
  case checkNf ga s nf of () -> (ty `appTy` nf, ne `appNe` nf)
inferElim _ (TySig s _, ne) ElimPr1 = (s, ne `elimNe` ElimPr1)
inferElim _ (TySig s t, ne) ElimPr2 = (t', ne `elimNe` ElimPr2)
  where t' = TyAbs s t `appTy` proj1 (NfNeu ne)
inferElim ga (TyTwo, ne) elim@(ElimTwo p t f) =
  case
    (checkTy ga p,
    checkNf ga (p `appTy` NfTru) t,
    checkNf ga (p `appTy` NfFls) f)
  of ((), (), ()) -> (p `appTy` NfNeu ne, ne `elimNe` elim)
inferElim _ _ (ElimRec _ _) = undefined

inferSp :: Eq a => Context a -> (Ty Nf a, Ne a) -> Sp Nf a -> Ty Nf a
inferSp ga tyNe (Sp elims) = fst $ foldl (inferElim ga) tyNe elims
