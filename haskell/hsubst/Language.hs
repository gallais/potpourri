{-# LANGUAGE DeriveFunctor #-}

module Language where

import Prelude.Extras

-------------------
-- Language
-------------------

newtype Scope f a = Scope { outScope :: f (Maybe a) }
  deriving (Functor)

newtype Sp f a = Sp { outSp :: [Elim f a] }
  deriving (Eq, Functor, Show)

data Elim f a =
    ElimApp (f a)
  | ElimPr1
  | ElimPr2
  | ElimBot (Ty f a)
  | ElimTwo (Ty f a) (f a) (f a)
  | ElimRec (Ty f a) (f a)
  deriving (Eq, Functor, Show)

data Da f a =
    DaVar
  | DaCst (Ty f a)
  | DaSig (Ty f a) (Scope (Da f) a)
  | DaAbs (Ty f a) (Scope (Da f) a)
  deriving (Eq, Functor, Show)

data Ty f a =
    TySet
  | TyAbs (Ty f a) (Scope (Ty f) a)
-- data
  | TyZro
  | TyOne
  | TyTwo
  | TySig (Ty f a) (Scope (Ty f) a)
-- interpretation
  | TyRec (Da f a)
  | TyFun (Da f a) (Ty f a)
-- lift
  | TyElt (f a)
  deriving (Functor)

data Tm a =
-- function spaces
    TmAbs (Scope Tm a)
-- neutral terms
  | TmVar a
  | TmApp (Tm a) (Ty Tm a) -- f : (T1 -> T2)
          (Sp Tm a)        -- $ ts
-- types
  | TmTyp (Ty Tm a)
-- constructors
  | TmInM (Tm a)
  | TmOne
  | TmTru
  | TmFls
  | TmSig (Tm a) (Tm a)
  deriving (Eq, Functor, Show)

-- Smart constructors for the top-level language

wkTm :: Tm a -> Tm (Maybe a)
wkTm = fmap Just

wkTy :: Functor f => Ty f a -> Ty f (Maybe a)
wkTy = fmap Just

lamTm :: Tm (Maybe a) -> Tm a
lamTm = TmAbs . Scope

piTm :: Ty f  a -> Ty f (Maybe a) -> Ty f a
piTm s = TyAbs s . Scope

arrTm :: Ty Tm a -> Ty Tm a -> Ty Tm a
arrTm s = piTm s . wkTy

-------------------
-- Canonical forms
-------------------

data Nf a =
-- function spaces
    NfAbs (Scope Nf a)
-- neutral terms
  | NfNeu (Ne a)
-- types
  | NfTyp (Ty Nf a)
-- constructors
  | NfInM (Nf a)
  | NfOne
  | NfTru
  | NfFls
  | NfSig (Nf a) (Nf a)
  deriving (Eq, Functor, Show)

data Ne a = Ne a (Sp Nf a)
  deriving (Eq, Functor, Show)

-- Smart constructors for the CL

varNe :: a -> Ne a
varNe v = Ne v $ Sp []

varNf :: a -> Nf a
varNf = NfNeu . varNe

lamNf :: Nf (Maybe a) -> Nf a
lamNf = NfAbs . Scope

piNf :: Ty Nf a -> Ty Nf (Maybe a) -> Ty Nf a
piNf a = TyAbs a . Scope

arrNf :: Ty Nf a -> Ty Nf a -> Ty Nf a
arrNf s = piNf s . wkTy

nfTy :: Ty Nf a -> Nf a
nfTy (TyElt t) = t
nfTy ty        = NfTyp ty

tyElt :: Nf a -> Ty Nf a
tyElt (NfTyp t) = t
tyElt ty        = TyElt ty

-- Weakening is a simple [fmap]
-- The subtle part is in the definition of [fmap]
-- for [Scope t]

wkNe :: Ne a -> Ne (Maybe a)
wkNe = fmap Just

wkNf :: Nf a -> Nf (Maybe a)
wkNf = fmap Just

-------------------
-- Extension of a Description
-------------------

funExt :: Da Nf a -> Ty Nf a -> Ty Nf a
funExt DaVar       x = x
funExt (DaCst ty)  _ = ty
funExt (DaSig a d) x = TySig a $ Scope $ funExt (outScope d) (wkTy x)
funExt (DaAbs a d) x = TyAbs a $ Scope $ funExt (outScope d) (wkTy x)

-------------------
-- Typeclass instances
-------------------

-- Eq
instance Eq1 Tm
instance Eq1 Nf

instance (Eq1 f) => Eq1 (Ty f) where
  TySet     ==# TySet     = True
  TyAbs a b ==# TyAbs s t = a ==# s && b == t
  TyZro     ==# TyZro     = True
  TyOne     ==# TyOne     = True
  TyTwo     ==# TyTwo     = True
  TySig a b ==# TySig s t = a ==# s && b == t
  TyRec d   ==# TyRec e   = d ==# e
  TyFun d x ==# TyFun e y = d ==# e && x ==# y
  TyElt t   ==# TyElt u   = t ==# u
  _         ==# _         = False

instance (Eq1 f) => Eq1 (Da f) where
  DaVar     ==# DaVar     = True
  DaCst t   ==# DaCst u   = t ==# u
  DaSig a d ==# DaSig b e = a ==# b && d == e
  DaAbs a d ==# DaAbs b e = a ==# b && d == e
  _         ==# _         = False

instance (Eq a, Eq1 f) => Eq (Ty f a) where
  (==) = (==#)
instance (Eq a, Eq1 f) => Eq (Scope f a) where
  Scope sc1 == Scope sc2 = sc1 ==# sc2

-- Show
instance Show1 Tm where showsPrec1 = showsPrec
instance Show1 Nf where showsPrec1 = showsPrec
instance (Show1 f) => Show1 (Ty f) where
  showsPrec1 i TySet       = showString "Set"
  showsPrec1 i (TyAbs a b) =
    showString "Π " . showsPrec1 i a .
    showString ". " . showsPrec1 i b
  showsPrec1 i TyZro       = showString "⊥"
  showsPrec1 i TyOne       = showString "⊤"
  showsPrec1 i TyTwo       = showString "𝔹"
  showsPrec1 i (TySig a b) =
    showString "Σ " . showsPrec1 i a .
    showString ". " . showsPrec1 i b
  showsPrec1 i (TyRec d)   = showString "μ " . showsPrec1 i d
  showsPrec1 i (TyFun d x) =
    showString "⟦" . showsPrec1 i d .
    showString "⟧" . showsPrec1 i x
  showsPrec1 i (TyElt t)   = showsPrec1 i t

instance (Show1 f, Show a) => Show (Ty f a) where
  show = show1

instance (Show1 f) => Show1 (Da f) where
  showsPrec1 i = showsPrec1 i . Lift1

instance (Show1 f) => Show1 (Scope f)
instance (Show a, Show1 f) => Show (Scope f a) where
  show (Scope sc) = show1 sc
