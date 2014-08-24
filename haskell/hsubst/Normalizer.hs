module Normalizer where

import Language
import Context
import HSubst
import Data.Void

------------------
-- Eta expansion
-------------------

neToNf :: Eq a => Ty Nf a -> Ne a -> Nf a
neToNf TyOne          _  = NfOne
neToNf (TySig a b)    ne = NfSig a' b'
  where
    a' = neToNf a $ elimNe ne ElimPr1
    b' = neToNf (TyAbs a b `appTy` a') $ elimNe ne ElimPr2
neToNf ty@(TyAbs s _) ne = lamNf body
  where body = neToNf (wkTy ty `appTy` var) $ wkNe ne `appNe` var
        var  = neToNf (wkTy s) $ varNe Nothing
neToNf _              ne = NfNeu ne

-------------------
-- Normalization
-- Implemented using Hereditary Substitution
-------------------

type Norm f a = f Tm a -> f Nf a

normScope :: Eq a => Norm f (Maybe a) ->
             Scope (f Tm) a -> Scope (f Nf) a
normScope norm = Scope . norm . outScope

normDa :: Eq a => Norm Da a
normDa DaVar       = DaVar
normDa (DaCst ty)  = DaCst $ normTy ty
normDa (DaSig a d) = normTy a `DaSig` normScope normDa d
normDa (DaAbs a d) = normTy a `DaAbs` normScope normDa d

normTy :: Eq a => Norm Ty a
normTy TySet       = TySet
normTy TyZro       = TyZro
normTy TyOne       = TyOne
normTy (TyAbs a b) = TyAbs (normTy a) $ normScope normTy b
normTy (TySig a b) = TySig (normTy a) $ normScope normTy b
normTy (TyRec dat) = TyRec $ normDa dat
normTy (TyFun d x) = funExt (normDa d) (normTy x)
normTy (TyElt elt) = tyElt $ norm TySet elt

norm :: Eq a => Ty Nf a -> Tm a -> Nf a
norm (TyElt (NfTyp ty)) tm = norm ty tm
norm (TyAbs _ t) (TmAbs b) = lamNf $ norm (outScope t) $ outScope b
norm ty (TmVar v) = neToNf ty $ varNe v
norm _ (TmApp f ty sp) = normSp (ty', norm ty' f) $ outSp sp
  where ty' = normTy ty
norm _ (TmTyp ty) = nfTy $ normTy ty
norm (TyRec d) (TmInM r) = NfInM $ norm (funExt d $ TyRec d) r
norm TyOne _     = NfOne
norm _     TmTru = NfTru
norm _     TmFls = NfFls
norm (TySig a b) (TmSig x y) = NfSig x' y'
  where x' = norm a x
        y' = norm (hSubstTy Nothing x' DropIt $ outScope b) y

normElim :: Eq a => (Ty Nf a, Nf a) -> Elim Tm a -> (Ty Nf a, Nf a)
normElim (ty@(TyAbs s _), f) (ElimApp tm) = (tnf, fnf)
  where nf  = norm s tm
        tnf = ty `appTy` nf
        fnf = f `appNf` nf
normElim (TySig a _, p) ElimPr1 = (a, p `elimNf` ElimPr1)
normElim (TySig _ b, p) ElimPr2 = (b', p `elimNf` ElimPr2)
  where b' = hSubstTy Nothing (p `elimNf` ElimPr1) DropIt $ outScope b
normElim (TyRec _, _) (ElimRec _ _) = undefined

normSp :: Eq a => (Ty Nf a, Nf a) -> [Elim Tm a] -> Nf a
normSp tyNf = snd . foldl normElim tyNf

normClosed :: Ty Nf Void -> Tm Void -> Nf Void
normClosed = norm
