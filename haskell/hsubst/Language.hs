{-# LANGUAGE DeriveFunctor #-}

module Language where

import Data.Void
import Data.Bifunctor
import Data.List
import Prelude.Extras

-------------------
-- Language
-------------------

newtype ScopeDa f a b = ScopeDa { outScopeDa :: f (Maybe a) b }
newtype ScopeTm f a b = ScopeTm { outScopeTm :: f a (Maybe b) }

newtype Sp f g a b = Sp { outSp :: [Elim f g a b] }
  deriving (Eq)

data Elim f g a b =
    ElimApp (f a b)
  | ElimPr1
  | ElimPr2
  | ElimBot (Ty g a b)
  | ElimTwo (Ty g a b) (f a b) (f a b)
  | ElimRec (ScopeDa (Ty g) a b) (Ty g a b) (f a b)

data Ty f a b =
    TySet
  | TyDat
  | TyAbs (Ty f a b) (ScopeTm (Ty f) a b)
-- data
  | TyZro
  | TyOne
  | TyTwo
  | TySig (Ty f a b) (ScopeTm (Ty f) a b)
-- interpretation
  | TyVar a
  | TyRec (ScopeDa (Ty f) a b)
  | TyFun (ScopeDa (Ty f) a b) (Ty f a b)
-- lift
  | TyElt (f a b)

tyAbs :: Ty f a b -> Ty f a (Maybe b) -> Ty f a b
tyAbs a = TyAbs a . ScopeTm

tyArr :: Bifunctor f => Ty f a b -> Ty f a b -> Ty f a b
tyArr a = tyAbs a . wkTy

data Tm a b =
-- function spaces
    TmAbs (ScopeTm Tm a b)
-- neutral terms
  | TmVar b
  | TmApp (Tm a b) (Ty Tm a b) -- f : (T1 -> T2)
          (Sp Tm Tm a b)       -- $ ts
-- types
  | TmTyp (Ty Tm a b)
-- constructors
  | TmInM (Tm a b)
  | TmOne
  | TmTru
  | TmFls
  | TmSig (Tm a b) (Tm a b)
  deriving (Eq, Show)

-- Smart constructors for the top-level language

wkTm :: Tm a b -> Tm a (Maybe b)
wkTm = second Just

wkTmDa :: Tm a b -> Tm (Maybe a) b
wkTmDa = first Just

wkTy :: Bifunctor f => Ty f a b -> Ty f a (Maybe b)
wkTy = second Just

wkTyDa :: Bifunctor f => Ty f a b -> Ty f (Maybe a) b
wkTyDa = first Just

lamTm :: Tm a (Maybe b) -> Tm a b
lamTm = TmAbs . ScopeTm

lamTm' :: Tm a b -> Tm a b
lamTm' = lamTm . wkTm

-------------------
-- Canonical forms
-------------------

data Nf a b =
-- function spaces
    NfAbs (ScopeTm Nf a b)
-- neutral terms
  | NfNeu (Ne a b)
-- types
  | NfTyp (Ty Ne a b)
-- constructors
  | NfInM (Nf a b)
  | NfOne
  | NfTru
  | NfFls
  | NfSig (Nf a b) (Nf a b)
  deriving (Eq, Show)

data Ne a b = Ne b (Sp Nf Ne a b)
  deriving (Eq)

-- Smart constructors for the CL

varNe :: b -> Ne a b
varNe v = Ne v $ Sp []

varNf :: b -> Nf a b
varNf = NfNeu . varNe

lamNf :: Nf a (Maybe b) -> Nf a b
lamNf = NfAbs . ScopeTm

lamNf' :: Nf a b -> Nf a b
lamNf' = lamNf . wkNf

nfTyp :: Ty Ne a b -> Nf a b
nfTyp (TyElt ty) = NfNeu ty
nfTyp ty         = NfTyp ty

tyElt :: Nf a b -> Ty Ne a b
tyElt (NfTyp t) = t
tyElt (NfNeu t) = TyElt t

-- Weakening is a simple [fmap]
-- The subtle part is in the definition of [fmap]
-- for [Scope t]

wkNeDa :: Ne a b -> Ne (Maybe a) b
wkNeDa = first Just

wkNe :: Ne a b -> Ne a (Maybe b)
wkNe = second Just

wkNfDa :: Nf a b -> Nf (Maybe a) b
wkNfDa = first Just

wkNf :: Nf a b -> Nf a (Maybe b)
wkNf = second Just

-------------------
-- Typeclass instances
-------------------

-- Eq
instance Eq2 Tm
instance Eq2 Ne
instance Eq2 Nf

instance (Eq2 f, Eq2 g) => Eq2 (Elim f g) where
  ElimApp t     ==## ElimApp u     = t ==## u
  ElimPr1       ==## ElimPr1       = True
  ElimPr2       ==## ElimPr2       = True
  ElimBot t     ==## ElimBot u     = t ==## u
  ElimTwo p t f ==## ElimTwo q u g = p ==## q && t ==## u && f ==## g
  ElimRec d p a ==## ElimRec e q b = d ==## e && p ==## q && a ==## b

instance Eq2 f => Eq2 (Ty f) where
  TySet     ==## TySet     = True
  TyAbs a b ==## TyAbs s t = a ==## s && b == t
  TyZro     ==## TyZro     = True
  TyOne     ==## TyOne     = True
  TyTwo     ==## TyTwo     = True
  TySig a b ==## TySig s t = a ==## s && b == t
  TyRec d   ==## TyRec e   = d == e
  TyFun d x ==## TyFun e y = d == e && x ==## y
  TyElt t   ==## TyElt u   = t ==## u
  _         ==## _         = False

instance Eq2 f => Eq2 (ScopeDa f) where
  ScopeDa sc1 ==## ScopeDa sc2 = sc1 ==## sc2

instance Eq2 f => Eq2 (ScopeTm f) where
  ScopeTm sc1 ==## ScopeTm sc2 = sc1 ==## sc2

instance (Eq2 f, Eq2 g, Eq a, Eq b) => Eq (Elim f g a b)
instance (Eq2 f, Eq a, Eq b) => Eq (Ty f a b)
instance (Eq2 f, Eq a, Eq b) => Eq (ScopeDa f a b)
instance (Eq2 f, Eq a, Eq b) => Eq (ScopeTm f a b)

-- Bifunctor

instance Bifunctor f => Bifunctor (ScopeDa f) where
  bimap f g = ScopeDa . bimap (fmap f) g . outScopeDa

instance Bifunctor f => Bifunctor (ScopeTm f) where
  bimap f g = ScopeTm . bimap f (fmap g) . outScopeTm

instance (Bifunctor f, Bifunctor g) => Bifunctor (Elim f g) where
  bimap f g (ElimApp t)       = ElimApp $ bimap f g t
  bimap _ _ ElimPr1           = ElimPr1
  bimap _ _ ElimPr2           = ElimPr2
  bimap f g (ElimBot p)       = ElimBot $ bimap f g p
  bimap f g (ElimTwo p l r)   =
    ElimTwo (bimap f g p) (bimap f g l) (bimap f g r)
  bimap f g (ElimRec d p alg) =
    ElimRec (bimap f g d) (bimap f g p) (bimap f g alg)

instance (Bifunctor f, Bifunctor g) => Bifunctor (Sp f g) where
  bimap f g = Sp . fmap (bimap f g) . outSp

instance Bifunctor f => Bifunctor (Ty f) where
  bimap _ _ TySet       = TySet
  bimap _ _ TyDat       = TyDat
  bimap f g (TyAbs a b) = TyAbs (bimap f g a) $ bimap f g b
  bimap _ _ TyZro       = TyZro
  bimap _ _ TyOne       = TyOne
  bimap _ _ TyTwo       = TyTwo
  bimap f g (TySig a b) = TySig (bimap f g a) $ bimap f g b
  bimap f _ (TyVar a)   = TyVar $ f a
  bimap f g (TyRec d)   = TyRec $ bimap f g d
  bimap f g (TyFun d x) = TyFun (bimap f g d) $ bimap f g x
  bimap f g (TyElt t)   = TyElt $ bimap f g t

instance Bifunctor Tm where
  bimap f g (TmAbs b)       = TmAbs $ bimap f g b
  bimap f g (TmVar v)       = TmVar $ g v
  bimap f g (TmApp t at sp) =
    TmApp (bimap f g t) (bimap f g at) (bimap f g sp)
  bimap f g (TmTyp ty)      = TmTyp $ bimap f g ty
  bimap f g (TmInM mu)      = TmInM $ bimap f g mu
  bimap f g TmOne           = TmOne
  bimap f g TmTru           = TmTru
  bimap f g TmFls           = TmFls
  bimap f g (TmSig a b)     = TmSig (bimap f g a) (bimap f g b)

instance Bifunctor Nf where
  bimap f g (NfAbs b)   = NfAbs $ bimap f g b
  bimap f g (NfNeu ne)  = NfNeu $ bimap f g ne
  bimap f g (NfTyp ty)  = NfTyp $ bimap f g ty
  bimap f g (NfInM r)   = NfInM $ bimap f g r
  bimap _ _ NfOne       = NfOne
  bimap _ _ NfTru       = NfTru
  bimap _ _ NfFls       = NfFls
  bimap f g (NfSig a b) = NfSig (bimap f g a) $ bimap f g b

instance Bifunctor Ne where
  bimap f g (Ne v sp) = Ne (g v) $ bimap f g sp

-- Show

instance Show2 Tm
instance Show2 Ne
instance Show2 Nf

instance (Show2 f, Show2 g, Show a, Show b) =>
         Show (Elim f g a b) where
   show (ElimApp t)     = show2 t
   show ElimPr1         = "π1"
   show ElimPr2         = "π2"
   show (ElimBot p)     = "⊥-elim " ++ show2 p
   show (ElimTwo p t f) = "guard " ++ show2 p ++ show2 t ++ show2 f
   show (ElimRec d p a) = "elim " ++ show2 d ++ show2 p ++ show2 a

instance (Show2 f, Show2 g, Show a, Show b) =>
         Show (Sp f g a b) where
  show (Sp [])  = ""
  show (Sp els) = ""

instance (Show a, Show b) => Show (Ne a b) where
  show (Ne v (Sp [])) = show v
  show (Ne v (Sp [arg])) = show v ++ " $ " ++ show arg
  show (Ne v sp) =
    show v ++ " $ [" ++ intercalate ", " (map show $ outSp sp) ++ "]"

instance (Show2 f) => Show2 (Ty f) where
  showsPrec2 i TySet       = showString "Set"
  showsPrec2 i TyDat       = showString "Dat"
  showsPrec2 i (TyAbs a b) =
    showString "Π " . showsPrec2 i a .
    showString ". " . showsPrec2 i b
  showsPrec2 i TyZro       = showString "⊥"
  showsPrec2 i TyOne       = showString "⊤"
  showsPrec2 i TyTwo       = showString "Bool"
  showsPrec2 i (TySig a b) =
    showString "Σ " . showsPrec2 i a .
    showString ". " . showsPrec2 i b
  showsPrec2 i (TyVar v)   = showsPrec i v
  showsPrec2 i (TyRec d)   = showString "μ " . showsPrec2 i d
  showsPrec2 i (TyFun d x) =
    showString "⟦" . showsPrec2 i d .
    showString "⟧" . showsPrec2 i x
  showsPrec2 i (TyElt t)   = showsPrec2 i t

instance (Show2 f, Show a, Show b) => Show (ScopeDa f a b) where
  show = show2 . outScopeDa

instance (Show2 f, Show a, Show b) => Show (ScopeTm f a b) where
  show = show2 . outScopeTm

instance (Show2 f, Show a, Show b) => Show (Ty f a b) where
  show = show2

instance (Show2 f, Show2 g) => Show2 (Sp f g)
instance (Show2 f, Show2 g) => Show2 (Elim f g)
instance Show2 f => Show2 (ScopeDa f)
instance Show2 f => Show2 (ScopeTm f)
