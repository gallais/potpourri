{-# LANGUAGE FlexibleInstances #-}

module HSubst where

import Data.Maybe

newtype Scope f a = Scope { outScope :: f (Maybe a) }

instance Eq a => Eq (Scope Nf a) where
  Scope sc1 == Scope sc2 = sc1 == sc2

data Nf a =
    NfPi (Nf a) (Scope Nf a)
  | NfLam (Scope Nf a)
  | NfSet
  | NfNe (Ne a)
  deriving Eq

data Ne a = NeApp a (Sp (Nf a))
  deriving Eq

newtype Sp a = Sp { outSp :: [a] }
  deriving Eq

varNe :: a -> Ne a
varNe v = NeApp v $ Sp []

varNf :: a -> Nf a
varNf = NfNe . varNe

instance Functor Nf where
  fmap f (NfPi s t) = NfPi (fmap f s) $ fmap f t
  fmap f (NfLam b)  = NfLam $ fmap f b
  fmap _ NfSet      = NfSet
  fmap f (NfNe ne)  = NfNe $ fmap f ne

instance Functor Ne where
  fmap f (NeApp v sp) = NeApp (f v) $ fmap (fmap f) sp

instance Functor Sp where
  fmap f (Sp sp) = Sp $ fmap f sp

instance Functor t => Functor (Scope t) where
  fmap f (Scope sc) = Scope $ fmap (fmap f) sc

wkNf :: Nf a -> Nf (Maybe a)
wkNf = fmap Just

-- HEREDITARY SUBSTITUTION

hSubstScope ::
  (Eq a, Eq b) =>
  a -> Nf b -> (a -> b) -> Scope Nf a -> Scope Nf b
hSubstScope v u rho (Scope sc) = Scope $ hSubstNf v' u' rho' sc
  where v'   = Just v
        u'   = fmap Just u
        rho' = fmap rho

hSubstNf :: (Eq a, Eq b) => a -> Nf b -> (a -> b) -> Nf a -> Nf b
hSubstNf v u rho (NfPi s t) = NfPi s' t'
  where s' = hSubstNf    v u rho s
        t' = hSubstScope v u rho t
hSubstNf v u rho (NfLam b)  = NfLam $ hSubstScope v u rho b
hSubstNf v u rho NfSet      = NfSet
hSubstNf v u rho (NfNe ne)  = hSubstNe v u rho ne

hSubstNe :: (Eq a, Eq b) => a -> Nf b -> (a -> b) -> Ne a -> Nf b
hSubstNe w u rho (NeApp v sp) = v' `hApp` sp'
  where v'  = hSubstVar w u rho v
        sp' = hSubstSp  w u rho sp

hSubstSp ::
  (Eq a, Eq b) =>
  a -> Nf b -> (a -> b) -> Sp (Nf a) -> Sp (Nf b)
hSubstSp v u rho = fmap (hSubstNf v u rho)

appNf :: Eq a => Nf a -> Nf a -> Nf a
appNf (NfPi _ b) u = hSubstNf Nothing u fromJust (outScope b)
appNf (NfLam b)  u = hSubstNf Nothing u fromJust (outScope b)

hApp :: Eq a => Nf a -> Sp (Nf a) -> Nf a
hApp nf (Sp sp) = foldl appNf nf sp

hSubstVar :: (Eq a, Eq b) => a -> Nf b -> (a -> b) -> a -> Nf b
hSubstVar v u rho w | v == w    = u
                    | otherwise = varNf $ rho w

-- TYPECHECKING
check :: Eq a => (a -> Nf a) -> Nf a -> Nf a -> ()
check gamma (NfPi s t) (NfLam b) = checkScope gamma s t b
check gamma NfSet      NfSet     = ()
check gamma ty         (NfNe ne)
  | ty == inferNe gamma ne       = ()

checkScope :: Eq a =>
  (a -> Nf a) -> Nf a -> Scope Nf a -> Scope Nf a -> ()
checkScope gamma sigma (Scope t) (Scope b) = check (wkNf . gamma') t b
  where gamma' Nothing  = sigma
        gamma' (Just v) = gamma v

inferNe :: Eq a => (a -> Nf a) -> Ne a -> Nf a
inferNe gamma (NeApp v sp) = inferSp gamma (gamma v) sp

inferSp :: Eq a => (a -> Nf a) -> Nf a -> Sp (Nf a) -> Nf a
inferSp gamma ty            (Sp [])        = ty
inferSp gamma ty@(NfPi s t) (Sp (hd : sp)) = inferSp gamma t' (Sp sp)
  where () = check gamma s hd
        t' = ty `appNf` hd
