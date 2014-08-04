module HSubst where

import Data.Maybe
import Language
import Context

hSubstScope :: (Eq a, Eq b) =>
               a -> Nf b -> Renaming a b -> Scope Nf a -> Scope Nf b
hSubstScope v u inc (Scope sc) = Scope $ hSubstNf v' u' ren' sc
  where v'   = Just v
        u'   = wkNf u
        ren' = KeepIt inc

hSubstNf :: (Eq a, Eq b) =>
            a -> Nf b -> Renaming a b -> Nf a -> Nf b
hSubstNf v u inc (NfPi s t) = NfPi s' t'
  where s' = hSubstNf    v u inc s
        t' = hSubstScope v u inc t
hSubstNf v u inc (NfLam b)  = NfLam $ hSubstScope v u inc b
hSubstNf v u inc NfSet      = NfSet
hSubstNf v u inc (NfNe ne)  = hSubstNe v u inc ne

hSubstNe :: (Eq a, Eq b) =>
            a -> Nf b -> Renaming a b -> Ne a -> Nf b
hSubstNe w u inc (NeApp v sp) = v' `hApp` sp'
  where v'  = hSubstVar w u inc v
        sp' = hSubstSp  w u inc sp

hSubstSp :: (Eq a, Eq b) =>
            a -> Nf b -> Renaming a b -> Sp (Nf a) -> Sp (Nf b)
hSubstSp v u inc = fmap (hSubstNf v u inc)


hSubstVar :: (Eq a, Eq b) =>
             a -> Nf b -> Renaming a b -> a -> Nf b
hSubstVar v u inc w | v == w    = u
                    | otherwise = varNf $ rename inc w

hSubst :: (Eq a) => Scope Nf a -> Nf a -> Nf a
hSubst b u = hSubstNf Nothing u DropIt $ outScope b


appNf :: (Eq a) => Nf a -> Nf a -> Nf a
appNf (NfPi _ b) u = hSubst b u
appNf (NfLam b)  u = hSubst b u

hApp :: (Eq a) => Nf a -> Sp (Nf a) -> Nf a
hApp nf (Sp sp) = foldl appNf nf sp
