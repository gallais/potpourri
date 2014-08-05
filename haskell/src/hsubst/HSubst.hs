module HSubst where

import Data.Maybe
import Language
import Context

--------------------
--- Hereditary Substitution
--------------------

hSubstScope :: (Eq a, Eq b) =>
               a -> Nf b -> Renaming a b -> Scope Nf a -> Scope Nf b
hSubstScope v u ren (Scope sc) = Scope $ hSubstNf v' u' ren' sc
  where v'   = Just v
        u'   = wkNf u
        ren' = KeepIt ren

hSubstNf :: (Eq a, Eq b) =>
            a -> Nf b -> Renaming a b -> Nf a -> Nf b
hSubstNf v u ren (NfPi s t) = NfPi s' t'
  where s' = hSubstNf    v u ren s
        t' = hSubstScope v u ren t
hSubstNf v u ren (NfLam b)  = NfLam $ hSubstScope v u ren b
hSubstNf v u ren NfSet      = NfSet
hSubstNf v u ren NfNat      = NfNat
hSubstNf v u ren NfZro      = NfZro
hSubstNf v u ren (NfSuc n)  = NfSuc $ hSubstNf v u ren n
hSubstNf v u ren (NfNe ne)  = hSubstNe v u ren ne

hSubstNe :: (Eq a, Eq b) =>
            a -> Nf b -> Renaming a b -> Ne a -> Nf b
hSubstNe w u ren (Ne v sp) = v' `hApp` sp'
  where v'  = hSubstVar w u ren v
        sp' = hSubstSp  w u ren sp

hSubstSp :: (Eq a, Eq b) =>
            a -> Nf b -> Renaming a b -> Sp Nf a -> Sp Nf b
hSubstSp v u ren (Sp sp) = Sp $ fmap (hSubstElim v u ren) sp

hSubstElim :: (Eq a, Eq b) =>
            a -> Nf b -> Renaming a b -> Elim Nf a -> Elim Nf b
hSubstElim v u ren (ElimApp t)      = ElimApp $ hSubstNf v u ren t
hSubstElim v u ren (ElimRec ty z s) = ElimRec (hS ty) (hS z) (hS s)
  where hS = hSubstNf v u ren

hSubstVar :: (Eq a, Eq b) =>
             a -> Nf b -> Renaming a b -> a -> Nf b
hSubstVar v u ren w | v == w    = u
                    | otherwise = varNf $ rename ren w

hSubst :: Eq a => Scope Nf a -> Nf a -> Nf a
hSubst b u = hSubstNf Nothing u DropIt $ outScope b

appNe :: Ne a -> Nf a -> Ne a
appNe ne = elimNe ne . ElimApp

appNf :: Eq a => Nf a -> Nf a -> Nf a
appNf (NfPi _ b) u = hSubst b u
appNf (NfLam b)  u = hSubst b u

recNf :: Eq a => Nf a -> Nf a -> Nf a -> Nf a -> Nf a
recNf ty s z NfZro     = z
recNf ty s z (NfSuc n) = s `appNf` n `appNf` recNf ty s z n
recNf ty s z (NfNe ne) = NfNe $ elimNe ne $ ElimRec ty s z

elimNe :: Ne a -> Elim Nf a -> Ne a
elimNe (Ne v (Sp sp)) elim = Ne v $ Sp $ sp ++ [elim]

elimNf :: Eq a => Nf a -> Elim Nf a -> Nf a
elimNf t (ElimApp u)      = t `appNf` u
elimNf n (ElimRec ty z s) = recNf ty z s n

hApp :: Eq a => Nf a -> Sp Nf a -> Nf a
hApp nf (Sp sp) = foldl elimNf nf sp
