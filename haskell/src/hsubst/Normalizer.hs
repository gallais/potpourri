module Normalizer where

import Language
import Context
import HSubst
import Data.Void

-------------------
-- Eta expansion
-------------------

neToNf :: Eq a => Nf a -> Ne a -> Nf a
neToNf ty@(NfPi s t) ne = lamNf body
  where body = neToNf (wkNf ty `appNf` s') $ wkNe ne `appNe` s'
        s'   = neToNf (wkNf s) $ varNe Nothing
neToNf _ ne = NfNe ne

-------------------
-- Normalization
-- Implemented using Hereditary Substitution
-------------------

tyIH :: Eq a => Nf a -> Nf a
tyIH ty = piNf NfNat $ arrNf (wkNf ty `appNf` var0) $
                              wkNf ty `appNf` NfSuc var0
  where var0 = varNf Nothing

norm :: Eq a => Context a -> Nf a -> Tm a -> Nf a
norm gamma ty (TmVar v) = neToNf (gamma `givesTypeTo` v) $ varNe v
norm gamma _  (TmPi s t) = NfPi s' $ Scope t'
  where s' = norm gamma NfSet s
        t' = norm (gamma .~ NfSet) NfSet $ outScope t
norm gamma (NfPi s t) (TmLam b) = lamNf body
  where body = norm (gamma .~. s) (outScope t) $ outScope b
norm gamma _ TmZro = NfZro
norm gamma _ (TmSuc n) = NfSuc $ norm gamma NfNat n
norm gamma _ TmNat = NfNat
norm gamma _ TmSet = NfSet
norm gamma _ (TmRec p s z n) = recNf p' s' z' $ norm gamma NfNat n
  where p' = norm gamma (arrNf NfNat NfSet) p
        s' = norm gamma (tyIH p') s
        z' = norm gamma (p' `appNf` NfZro) z
norm gamma _ (TmApp f ty ts) = normSp gamma (ty', f') $ outSp ts
  where ty' = norm gamma NfSet ty
        f'  = norm gamma ty' f

normElim :: Eq a =>
  Context a -> (Nf a, Nf a) -> Elim Tm a -> (Nf a, Nf a)
normElim gamma (NfPi s t, f) (ElimApp tm) = (tnf, fnf)
  where nf  = norm gamma s tm
        tnf = t `hSubst` nf
        fnf = f `appNf` nf
normElim gamma (NfNat, n) (ElimRec p s z) = (pn, elimN)
  where p'    = norm gamma (arrNf NfNat NfSet) p
        s'    = norm gamma (tyIH p') s
        z'    = norm gamma (p' `appNf` NfZro) z
        pn    = p' `appNf` n
        elimN = recNf p' s' z' n

normSp :: Eq a =>
  Context a -> (Nf a, Nf a) -> [Elim Tm a] -> Nf a
normSp gamma tyNf = snd . foldl (normElim gamma) tyNf

normClosed :: Nf Void -> Tm Void -> Nf Void
normClosed = norm empty
