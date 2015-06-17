{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

module DBTerm where

import Data.Void

data Nat = Zero | Succ Nat
  deriving Show

data DBTerm =
    DBVar Nat
  | DBApp DBTerm DBTerm
  | DBLam DBTerm
  | DBPi  DBTerm DBTerm
  | DBSet
  | DBNat
  | DBSucc DBTerm
  | DBZero

data SNat (n :: Nat) where
  SZero :: SNat Zero
  SSucc :: SNat n -> SNat (Succ n)

data SDBTerm (t :: DBTerm) where
  SDBVar :: SNat n -> SDBTerm (DBVar n)
  SDBApp :: SDBTerm t -> SDBTerm u -> SDBTerm (DBApp t u)
  SDBLam :: SDBTerm t -> SDBTerm (DBLam t)
  SDBPi  :: SDBTerm a -> SDBTerm b -> SDBTerm (DBPi a b)
  SDBSet :: SDBTerm DBSet
  SDBNat :: SDBTerm DBNat
  SDBSucc :: SDBTerm n -> SDBTerm (DBSucc n)
  SDBZero :: SDBTerm DBZero

newtype Constant a (n :: Nat) = Constant { runConstant :: a }

data Extend' (r :: Nat -> *) (t :: *) (n :: Nat) where
  Here  :: t   -> Extend' r t Zero
  There :: r n -> Extend' r t (Succ n)

data SRho (k :: Nat -> *) where
  SBase   :: SRho (Constant Void)
  SExtend :: SRho rho -> SDBTerm a -> SRho (Extend' rho (El a rho))

data Nf    = NfElNat ElNat | NfPi Nf Nf | NfLam Nf | NfSet | NfNat | NfNe Ne
  deriving Show
data ElNat = ElZero | ElSucc ElNat | ElNe Ne
  deriving Show
data Ne    = NeVar Nat | NeApp Ne Nf
  deriving Show

type family El (t :: DBTerm) (rho :: Nat -> *) where
  El (DBPi a b) rho = El a rho -> El b (Extend' rho (El a rho))
  El (DBVar n)  rho = rho n
  El DBSet      rho = Nf
  El DBNat      rho = ElNat

reflectVar :: SNat n -> SRho rho -> Ne -> El (DBVar n) rho
reflectVar SZero     (SExtend rho a) ne = Here  $ reflect a rho ne
reflectVar (SSucc n) (SExtend rho a) ne = There $ reflectVar n rho ne

reifyVar :: SRho rho -> El (DBVar n) rho -> Nf
reifyVar (SExtend rho a) (Here t)  = reify a rho t
reifyVar (SExtend rho a) (There t) = reifyVar rho t

reflect :: SDBTerm t -> SRho rho -> Ne -> El t rho
reflect (SDBPi a b) rho f = \ x -> reflect b (SExtend rho a) $ NeApp f $ reify a rho x
reflect (SDBVar v)  rho t = reflectVar v rho t
reflect SDBSet      rho s = NfNe s
reflect SDBNat      rho n = ElNe n

reify :: SDBTerm t -> SRho rho -> El t rho -> Nf
reify (SDBPi a b) rho f = NfLam $ reify b (SExtend rho a) $ f $ reflect a rho (NeVar Zero)
reify (SDBVar v)  rho t = reifyVar rho t
reify SDBSet      rho s = s
reify SDBNat      rho n = NfElNat n

identity :: Nf
identity = reify (SDBPi SDBSet (SDBPi (SDBVar SZero) (SDBVar (SSucc SZero)))) SBase $ \ ty e -> There e
