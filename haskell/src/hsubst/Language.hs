module Language where

import Prelude.Extras

-------------------
-- Language
-------------------

data Tm a =
    TmPi (Tm a) (Scope Tm a)
  | TmLam (Scope Tm a)
  | TmSet
  | TmVar a
  | TmApp (Tm a) (Tm a) -- f : (T1 -> T2)
          (Tm a)        -- $ t

-- Smart constructors for the top-level language

lamTm :: Tm (Maybe a) -> Tm a
lamTm = TmLam . Scope

piTm :: Tm a -> Tm (Maybe a) -> Tm a
piTm s = TmPi s . Scope

-------------------
-- Canonical forms
-------------------

newtype Scope f a = Scope { outScope :: f (Maybe a) }

data Nf a =
    NfPi (Nf a) (Scope Nf a)
  | NfLam (Scope Nf a)
  | NfSet
  | NfNe (Ne a)
  deriving (Eq, Show)

data Ne a = NeApp a (Sp (Nf a))
  deriving (Eq, Show)

newtype Sp a = Sp { outSp :: [a] }
  deriving (Eq, Show)

-- Smart constructors for the CL

varNe :: a -> Ne a
varNe v = NeApp v $ Sp []

varNf :: a -> Nf a
varNf = NfNe . varNe

lamNf :: Nf (Maybe a) -> Nf a
lamNf = NfLam . Scope

piNf :: Nf a -> Nf (Maybe a) -> Nf a
piNf s = NfPi s . Scope

-- Weakening is a simple [fmap]
-- The subtle part is in the definition of [fmap]
-- for [Scope t]

wkNe :: Ne a -> Ne (Maybe a)
wkNe = fmap Just

wkNf :: Nf a -> Nf (Maybe a)
wkNf = fmap Just

-------------------
-- Typeclass instances
-------------------

-- Eq (most of it is derived)
instance Eq1   Nf

instance (Eq a, Eq1 f) => Eq (Scope f a) where
  Scope sc1 == Scope sc2 = sc1 ==# sc2

-- Functor
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

-- Show
instance Show1 Nf

instance (Show a, Show1 f) => Show (Scope f a) where
  show (Scope sc) = show1 sc

