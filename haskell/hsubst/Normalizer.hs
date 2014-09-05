{-# LANGUAGE RankNTypes, KindSignatures #-}

module Normalizer where

import Language
import Context
import HSubst
import Data.Bifunctor
import Data.Void

------------------
-- Eta expansion
-------------------

neToNf :: (Eq a, Eq b) => Ty Ne a b -> Ne a b -> Nf a b
neToNf TyOne          _  = NfOne
neToNf (TySig a b)    ne = NfSig a' b'
  where
    a' = neToNf a $ elimNe ne ElimPr1
    b' = neToNf (TyAbs a b `appTy` a') $ elimNe ne ElimPr2
neToNf ty@(TyAbs s _) ne = lamNf body
  where body = neToNf (wkTy ty `appTy` var) $ wkNe ne `appNe` var
        var  = neToNf (wkTy s) $ varNe Nothing
neToNf _              ne = NfNeu ne

belowTy :: (Eq a, Eq b) =>
  ScopeDa (Ty Ne) a b -> Ty Ne a b -> Ty Ne (Maybe a) b ->
  Nf a b -> Ty Ne a b
belowTy d ty TyOne _ = TyOne
belowTy d ty pi@(TyAbs a _) f = tyAbs a' $ belowTy d' (wkTy ty) ba fa
  where d' = ScopeDa $ wkTy $ outScopeDa d
    -- a *has to* be TyVar-free!
        a' = hSubstTy (SubstDa Nothing TyOne) DropItDa a
        ba = wkTy pi `appTy` varNf Nothing
        fa = wkNf f `appNf` varNf Nothing
belowTy d ty (TySig a b) p = belowTy d ty ba $ proj2 p
  where ba = TyAbs a b `appTy` wkNfDa (proj1 p)
belowTy d ty (TyVar Nothing) x = ty `appTy` x

ihTy :: (Eq a, Eq b) => ScopeDa (Ty Ne) a b -> Ty Ne a b -> Ty Ne a b
ihTy d p =
  tyAbs (d `funExt` TyRec d) $
  tyArr (belowTy d' (wkTy p) (wkTy $ outScopeDa d) $ varNf Nothing) $
  wkTy p `appTy` NfInM (varNf Nothing)
  where d' = ScopeDa $ wkTy $ outScopeDa d

-------------------
-- Normalization
-- Implemented using Hereditary Substitution
-------------------

type Norm f a b = f Tm a b -> f Nf a b

normScopeTm :: Eq a =>
  forall (f :: (* -> * -> *) -> * -> * -> *).
  (f g a (Maybe b) -> f h a (Maybe b)) ->
  ScopeTm (f g) a b -> ScopeTm (f h) a b
normScopeTm norm = ScopeTm . norm . outScopeTm

normScopeDa :: Eq a =>
  forall (f :: (* -> * -> *) -> * -> * -> *).
  (f g (Maybe a) b -> f h (Maybe a) b) ->
  ScopeDa (f g) a b -> ScopeDa (f h) a b
normScopeDa norm = ScopeDa . norm . outScopeDa


normTy :: (Eq a, Eq b) => Ty Tm a b -> Ty Ne a b
normTy TySet       = TySet
normTy TyDat       = TyDat
normTy TyZro       = TyZro
normTy TyOne       = TyOne
normTy TyTwo       = TyTwo
normTy (TyAbs a b) = TyAbs (normTy a) $ normScopeTm normTy b
normTy (TySig a b) = TySig (normTy a) $ normScopeTm normTy b
normTy (TyVar v)   = TyVar v
normTy (TyRec dat) = TyRec $ normScopeDa normTy dat
normTy (TyFun d x) = normScopeDa normTy d `funExt` normTy x
normTy (TyElt elt) = tyElt $ norm TySet elt

norm :: (Eq a, Eq b) => Ty Ne a b -> Tm a b -> Nf a b
norm (TyAbs _ t) (TmAbs b) = lamNf $ outScopeTm t `norm` outScopeTm b
norm ty (TmVar v) = neToNf ty $ varNe v
norm _ (TmApp f ty sp) = normSp (ty', norm ty' f) $ outSp sp
  where ty' = normTy ty
norm _ (TmTyp ty) = nfTyp $ normTy ty
norm (TyRec d) (TmInM r) = NfInM $ norm (funExt d $ TyRec d) r
norm TyOne _     = NfOne
norm _     TmTru = NfTru
norm _     TmFls = NfFls
norm (TySig a b) (TmSig x y) = NfSig x' y'
  where x' = norm a x
        y' = norm (hSubstTy (SubstTm Nothing x') DropItTm $ outScopeTm b) y

normElim :: (Eq a, Eq b) =>
  (Ty Ne a b, Nf a b) -> Elim Tm Tm a b -> (Ty Ne a b, Nf a b)
normElim (ty@(TyAbs s _), f) (ElimApp tm) = (tnf, fnf)
  where nf  = norm s tm
        tnf = ty `appTy` nf
        fnf = f `appNf` nf
normElim (TySig a _, p) ElimPr1 = (a, proj1 p)
normElim (TySig _ b, p) ElimPr2 = (b', proj2 p)
  where b' = hSubstTy (SubstTm Nothing $ proj1 p) DropItTm $ outScopeTm b
normElim (TyTwo , b) (ElimTwo p t f) = (p' `appTy` b, ifte)
  where ifte = ifTE p' b tru fls
        p'   = normTy p
        tru  = norm (p' `appTy` NfTru) t
        fls  = norm (p' `appTy` NfFls) f
normElim (TyRec d, x) (ElimRec _ ty alg) = (ty' `appTy` x, val)
  where
    ty' = normTy ty
    val = recNf d ty' (norm (ihTy d ty') alg) x

normSp :: (Eq a, Eq b) =>
          (Ty Ne a b, Nf a b) -> [Elim Tm Tm a b] -> Nf a b
normSp tyNf = snd . foldl normElim tyNf

normClosed :: Ty Ne Void Void -> Tm Void Void -> Nf Void Void
normClosed = norm
