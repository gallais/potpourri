module TypeChecking where

import Language
import Context
import HSubst

-------------------
-- Bidirectional Typechecking
-------------------

-- type-checking for Normal Forms

check :: Eq a => Context a -> Nf a -> Nf a -> ()
check gamma (NfPi s t) (NfLam b)  = check (gamma .~. s) t' b'
  where t' = outScope t
        b' = outScope b
check gamma NfSet      NfSet      = ()
check gamma NfSet      NfNat      = ()
check gamma NfNat      NfZro      = ()
check gamma NfNat      (NfSuc n)  = check gamma NfNat n
check gamma NfSet      (NfPi s t) =
  case check gamma NfSet s of
    () -> check (gamma .~. s) NfSet $ outScope t
check gamma ty         (NfNe ne)
  | ty == inferNe gamma ne        = ()

-- type-inference for Neutral ones

inferNe :: Eq a => Context a -> Ne a -> Nf a
inferNe gamma (Ne v sp) = inferSp gamma (ty, varNe v) sp
  where ty = gamma `givesTypeTo` v

inferElim :: Eq a =>
  Context a -> (Nf a, Ne a) -> Elim Nf a -> (Nf a, Ne a)
inferElim gamma (NfPi s t, ne) (ElimApp nf) =
  (t `hSubst` nf, ne `appNe` nf)
inferElim gamma (NfNat, te) (ElimRec p s z) =
  (p `appNf` NfNe te, te `elimNe` ElimRec p s z)

inferSp :: Eq a => Context a -> (Nf a, Ne a) -> Sp Nf a -> Nf a
inferSp gamma tyNe (Sp elims) = fst $ foldl alg tyNe elims
  where alg = inferElim gamma
