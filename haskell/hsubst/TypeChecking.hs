module TypeChecking where

import Language
import Context
import HSubst

-------------------
-- Bidirectional Typechecking
-------------------

checkTyClosed :: (Eq a, Eq b, Show a, Show b) => Ty Nf a b -> ()
checkTyClosed TySet       = ()
checkTyClosed TyDat       = ()
checkTyClosed (TyAbs a b) =
  checkTyClosed a `seq` checkTyClosed $ outScopeTm b
checkTyClosed TyZro       = ()
checkTyClosed TyOne       = ()
checkTyClosed TyTwo       = ()
checkTyClosed (TySig a b) =
  checkTyClosed a `seq` checkTyClosed $ outScopeTm b
checkTyClosed (TyRec r)   = checkTyClosed r'
  where r' = hSubstTy (SubstDa Nothing TyZro) DropItDa $ outScopeDa r
checkTyClosed (TyFun d x) = checkTyClosed d' `seq` checkTyClosed x
  where d' = hSubstTy (SubstDa Nothing TyZro) DropItDa $ outScopeDa d
checkTyClosed (TyElt t)   = checkNfClosed t

checkNfClosed :: (Eq a, Eq b, Show a, Show b) => Nf a b -> ()
checkNfClosed = undefined

-- type-checking for Normal Forms

checkTy :: (Eq a, Eq b, Show a, Show b) => Context a b -> Ty Nf a b -> ()
checkTy ga TySet       = ()
checkTy ga TyDat       = ()
checkTy ga (TyAbs a b) =
  checkTy ga a `seq` checkTy (ga .~. a) $ outScopeTm b
checkTy ga TyZro       = ()
checkTy ga TyOne       = ()
checkTy ga TyTwo       = ()
checkTy ga (TySig a b) =
  checkTy ga a `seq` checkTy (ga .~. a) $ outScopeTm b
checkTy ga (TyRec r)   = undefined --checkTy ga $ outScopeDa r
checkTy ga (TyFun d x) =
  {- checkTy ga (outScopeDa d) `seq` -} checkTy ga x
checkTy ga (TyElt t)   = checkNf ga TySet t

checkNf :: (Eq a, Eq b, Show a, Show b) => Context a b -> Ty Nf a b -> Nf a b -> ()
checkNf ga (TyElt (NfTyp ty)) te = checkNf ga ty te
checkNf ga (TyAbs s t) (NfAbs b) = checkNf (ga .~. s) t' b'
  where t' = outScopeTm t
        b' = outScopeTm b
checkNf ga TySet (NfTyp ty) = checkTy ga ty
checkNf ga (TyRec d) (NfInM r) = checkNf ga (funExt d (TyRec d)) r
checkNf _ TyOne NfOne = ()
checkNf _ TyTwo NfTru = ()
checkNf _ TyTwo NfFls = ()
checkNf ga (TySig s t) (NfSig a b) =
  checkNf ga s a `seq` checkNf ga (TyAbs s t `appTy` a) b
checkNf ga ty (NfNeu ne)
  | ty == inferNe ga ne = ()

-- type-inference for Neutral Terms

inferNe :: (Eq a, Eq b, Show a, Show b) => Context a b -> Ne a b -> Ty Nf a b
inferNe ga (Ne v sp) = inferSp ga (ga `givesTypeTo` v, varNe v) sp

inferElim :: (Eq a, Eq b, Show a, Show b) =>
  Context a b -> (Ty Nf a b, Ne a b) -> Elim Nf a b -> (Ty Nf a b, Ne a b)
inferElim ga (ty@(TyAbs s _), ne) (ElimApp nf) =
  case checkNf ga s nf of () -> (ty `appTy` nf, ne `appNe` nf)
inferElim _ (TySig s _, ne) ElimPr1 = (s, ne `elimNe` ElimPr1)
inferElim _ (TySig s t, ne) ElimPr2 = (t', ne `elimNe` ElimPr2)
  where t' = TyAbs s t `appTy` proj1 (NfNeu ne)
inferElim ga (TyTwo, ne) elim@(ElimTwo p t f) =
        checkTy ga p
  `seq` checkNf ga (p `appTy` NfTru) t
  `seq` checkNf ga (p `appTy` NfFls) f
  `seq` (p `appTy` NfNeu ne, ne `elimNe` elim)
inferElim _ _ (ElimRec _ _) = undefined

inferSp :: (Eq a, Eq b, Show a, Show b) =>
  Context a b -> (Ty Nf a b, Ne a b) -> Sp Nf a b -> Ty Nf a b
inferSp ga tyNe (Sp elims) = fst $ foldl (inferElim ga) tyNe elims
