module Normalizer where

import Language
import Context
import HSubst
import Data.Bifunctor
import Data.Void

------------------
-- Eta expansion
-------------------

neToNf :: (Eq a, Eq b) => Ty Nf a b -> Ne a b -> Nf a b
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

type Norm f a b = f Tm a b -> f Nf a b

normScopeTm :: Eq a => Norm f a (Maybe b) ->
             ScopeTm (f Tm) a b -> ScopeTm (f Nf) a b
normScopeTm norm = ScopeTm . norm . outScopeTm

normScopeDa :: Eq a => Norm f (Maybe a) b ->
             ScopeDa (f Tm) a b -> ScopeDa (f Nf) a b
normScopeDa norm = ScopeDa . norm . outScopeDa

normTy :: (Eq a, Eq b) => Norm Ty a b
normTy TySet       = TySet
normTy TyDat       = TyDat
normTy TyZro       = TyZro
normTy TyOne       = TyOne
normTy (TyAbs a b) = TyAbs (normTy a) $ normScopeTm normTy b
normTy (TySig a b) = TySig (normTy a) $ normScopeTm normTy b
normTy (TyRec dat) = TyRec $ normScopeDa normTy dat
normTy (TyFun d x) = normScopeDa normTy d `funExt` normTy x
normTy (TyElt elt) = tyElt $ norm TySet elt

norm :: (Eq a, Eq b) => Ty Nf a b -> Tm a b -> Nf a b
norm (TyElt (NfTyp ty)) tm = norm ty tm
norm (TyAbs _ t) (TmAbs b) = lamNf $ outScopeTm t `norm` outScopeTm b
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
        y' = norm (hSubstTy (SubstTm Nothing x') DropItTm $ outScopeTm b) y

normElim :: (Eq a, Eq b) =>
  (Ty Nf a b, Nf a b) -> Elim Tm a b -> (Ty Nf a b, Nf a b)
normElim (ty@(TyAbs s _), f) (ElimApp tm) = (tnf, fnf)
  where nf  = norm s tm
        tnf = ty `appTy` nf
        fnf = f `appNf` nf
normElim (TySig a _, p) ElimPr1 = (a, p `elimNf` ElimPr1)
normElim (TySig _ b, p) ElimPr2 = (b', p `elimNf` ElimPr2)
  where b' = hSubstTy (SubstTm Nothing (p `elimNf` ElimPr1)) DropItTm $ outScopeTm b
normElim (TyRec _, _) (ElimRec _ _) = undefined

normSp :: (Eq a, Eq b) =>
          (Ty Nf a b, Nf a b) -> [Elim Tm a b] -> Nf a b
normSp tyNf = snd . foldl normElim tyNf

normClosed :: Ty Nf Void Void -> Tm Void Void -> Nf Void Void
normClosed = norm
