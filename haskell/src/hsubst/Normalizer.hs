module Normalizer where

import Language
import Context
import HSubst
import Data.Void

-------------------
-- Eta expansion
-------------------

appNe :: Ne a -> Nf a -> Ne a
appNe (NeApp v (Sp sp)) nf = NeApp v $ Sp $ sp ++ [nf]

neToNf :: Eq a => Nf a -> Ne a -> Nf a
neToNf ty@(NfPi s t) ne = lamNf body
  where body = neToNf (wkNf ty `appNf` s') $ wkNe ne `appNe` s'
        s'   = neToNf (wkNf s) $ varNe Nothing
neToNf _ ne = NfNe ne

-------------------
-- Normalization
-- Implemented using Hereditary Substitution
-------------------

norm :: Eq a => Context a -> Nf a -> Tm a -> Nf a
norm gamma ty (TmVar v)  = neToNf (gamma `givesTypeTo` v) $ varNe v
norm gamma _  (TmPi s t) = NfPi s' $ Scope t'
  where s' = norm gamma NfSet s
        t' = norm (gamma .~ NfSet) NfSet $ outScope t
norm gamma (NfPi s t) (TmLam b)  = lamNf body
  where body = norm (gamma .~. s) (outScope t) $ outScope b
norm gamma _ TmSet = NfSet
norm gamma _ (TmApp f ty x) = f' `appNf` x'
  where (NfPi s t) = norm gamma NfSet ty
        f'         = norm gamma (NfPi s t) f
        x'         = norm gamma s x

normClosed :: Nf Void -> Tm Void -> Nf Void
normClosed = norm empty
