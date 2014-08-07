module Language where

import Prelude.Extras

-------------------
-- Language
-------------------

data Tm a =
    TmPi (Tm a) (Scope Tm a)
  | TmLam (Scope Tm a)
  | TmNat
  | TmZro
  | TmSuc (Tm a)
  | TmSet
  | TmRec (Tm a) (Tm a) (Tm a) (Tm a)
  | TmVar a
  | TmApp (Tm a) (Tm a) -- f : (T1 -> T2)
          (Sp Tm a)        -- $ ts
  deriving (Eq, Show)

-- Smart constructors for the top-level language

wkTm :: Tm a -> Tm (Maybe a)
wkTm = fmap Just

lamTm :: Tm (Maybe a) -> Tm a
lamTm = TmLam . Scope

piTm :: Tm a -> Tm (Maybe a) -> Tm a
piTm s = TmPi s . Scope

arrTm :: Tm a -> Tm a -> Tm a
arrTm s = piTm s . wkTm

-------------------
-- Canonical forms
-------------------

newtype Scope f a = Scope { outScope :: f (Maybe a) }

newtype Sp f a = Sp { outSp :: [Elim f a] }
  deriving (Eq, Show)

data Elim f a =
    ElimApp (f a)
  | ElimRec (f a) (f a) (f a)
  deriving (Eq, Show)

data Nf a =
    NfPi (Nf a) (Scope Nf a)
  | NfLam (Scope Nf a)
  | NfSet
  | NfNat
  | NfZro
  | NfSuc (Nf a)
  | NfNe (Ne a)
  deriving (Eq, Show)

data Ne a = Ne a (Sp Nf a)
  deriving (Eq, Show)


-- Smart constructors for the CL

varNe :: a -> Ne a
varNe v = Ne v $ Sp []

varNf :: a -> Nf a
varNf = NfNe . varNe

lamNf :: Nf (Maybe a) -> Nf a
lamNf = NfLam . Scope

piNf :: Nf a -> Nf (Maybe a) -> Nf a
piNf s = NfPi s . Scope

arrNf :: Nf a -> Nf a -> Nf a
arrNf s = piNf s . wkNf

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
instance Eq1   Tm

instance (Eq a, Eq1 f) => Eq (Scope f a) where
  Scope sc1 == Scope sc2 = sc1 ==# sc2

-- Functor
instance Functor Tm where
  fmap f (TmPi s t)      = TmPi (fmap f s) (fmap f t)
  fmap f (TmLam b)       = TmLam $ fmap f b
  fmap _ TmNat           = TmNat
  fmap _ TmSet           = TmSet
  fmap _ TmZro           = TmZro
  fmap f (TmSuc n)       = TmSuc $ fmap f n
  fmap f (TmVar a)       = TmVar $ f a
  fmap f (TmApp v ty ts) = TmApp (fmap f v) (fmap f ty) (fmap f ts)
  fmap f (TmRec p s z n) =
    TmRec (fmap f p) (fmap f s) (fmap f z) (fmap f n)

instance Functor Nf where
  fmap f (NfPi s t) = NfPi (fmap f s) $ fmap f t
  fmap f (NfLam b)  = NfLam $ fmap f b
  fmap _ NfSet      = NfSet
  fmap _ NfNat      = NfNat
  fmap _ NfZro      = NfZro
  fmap f (NfSuc n)  = NfSuc $ fmap f n
  fmap f (NfNe ne)  = NfNe $ fmap f ne

instance Functor Ne where
  fmap f (Ne v sp) = Ne (f v) $ fmap f sp

instance Functor f => Functor (Sp f) where
  fmap f (Sp sp) = Sp $ fmap (fmap f) sp

instance Functor f => Functor (Elim f) where
  fmap f (ElimApp u)      = ElimApp $ fmap f u
  fmap f (ElimRec ty z s) = ElimRec (fmap f ty) (fmap f z) (fmap f z)

instance Functor t => Functor (Scope t) where
  fmap f (Scope sc) = Scope $ fmap (fmap f) sc

-- Show
instance Show1 Nf
instance Show1 Tm

instance (Show a, Show1 f) => Show (Scope f a) where
  show (Scope sc) = show1 sc

