module HSubst where

import Language
import Context

-------------------
-- Hereditary Substitution
-------------------

hSubstScope ::
  (Eq a, Eq b) =>
  a -> Nf b -> Renaming a b -> Scope Nf a -> Scope Nf b
hSubstScope v u ren (Scope sc) = Scope $ hSubstNf v' u' ren' sc
  where v'   = Just v
        u'   = fmap Just u
        ren' = wkRen ren

hSubstNf :: (Eq a, Eq b) => a -> Nf b -> Renaming a b -> Nf a -> Nf b
hSubstNf v u ren (NfPi s t) = NfPi s' t'
  where s' = hSubstNf    v u ren s
        t' = hSubstScope v u ren t
hSubstNf v u ren (NfLam b)  = NfLam $ hSubstScope v u ren b
hSubstNf v u ren NfSet      = NfSet
hSubstNf v u ren (NfNe ne)  = hSubstNe v u ren ne

hSubstNe :: (Eq a, Eq b) => a -> Nf b -> Renaming a b -> Ne a -> Nf b
hSubstNe w u ren (NeApp v sp) = v' `hApp` sp'
  where v'  = hSubstVar w u ren v
        sp' = hSubstSp  w u ren sp

hSubstSp ::
  (Eq a, Eq b) =>
  a -> Nf b -> Renaming a b -> Sp (Nf a) -> Sp (Nf b)
hSubstSp v u ren = fmap (hSubstNf v u ren)

hSubst :: Eq a => Scope Nf a -> Nf a -> Nf a
hSubst b u = hSubstNf Nothing u dropFst $ outScope b

appNf :: Eq a => Nf a -> Nf a -> Nf a
appNf (NfPi _ b) u = hSubst b u
appNf (NfLam b)  u = hSubst b u

hApp :: Eq a => Nf a -> Sp (Nf a) -> Nf a
hApp nf (Sp sp) = foldl appNf nf sp

hSubstVar :: (Eq a, Eq b) => a -> Nf b -> Renaming a b -> a -> Nf b
hSubstVar v u ren w | v == w    = u
                    | otherwise = varNf $ ren `givesNameTo` w
