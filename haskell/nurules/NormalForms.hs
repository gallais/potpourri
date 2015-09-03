{-# OPTIONS  -Wall          #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}

module NormalForms where

import Data.Sequence

import Context
import qualified Language as TM
import Semantics()

type Type (g :: Context) = Nf g

data Nf (g :: Context) =
    Bnd (Binder g) (Nf ('Bind g))
  | Zro
  | Suc (Nf g)
  | Emb (Ne g)
  | Nat
  | Set
  deriving Eq

data Ne (g :: Context) = Cut (Var g) (Spine g)
  deriving Eq

newtype Spine g = Spine { unSpine :: Seq (Elim g) }
  deriving Eq

data Elim (g :: Context) =
    App (Nf g)
  | Rec (Type g) (Nf g) (Nf g)
  deriving Eq

data Binder (g :: Context) =
    Lam
  | Pi  (Type g)
  deriving Eq

var :: Var g -> Nf g
var v = Emb $ Cut v $ Spine empty

instance Monoid (Spine g) where
  mempty         = Spine empty
  mappend sp sp' = Spine $ unSpine sp >< unSpine sp'

renamingNe :: Renaming g d -> Ne g -> Ne d
renamingNe = undefined

renamingNf :: Renaming g d -> Nf g -> Nf d
renamingNf = undefined

renamingElim :: Renaming g d -> Elim g -> Elim d
renamingElim ren (App u)      = App $ renamingNf ren u
renamingElim ren (Rec ty s z) = Rec (rnf ty) (rnf s) (rnf z)
  where rnf = renamingNf ren

renamingSpine :: Renaming g d -> Spine g -> Spine d
renamingSpine ren = Spine . fmap (renamingElim ren) . unSpine

-- Normal forms are a subset of the language, obviously
eraseNf :: Nf g -> TM.Check g
eraseNf (Bnd bd t) = TM.Bnd (eraseBinder bd) (eraseNf t)
eraseNf Zro        = TM.Zro
eraseNf (Suc m)    = TM.Suc $ eraseNf m
eraseNf (Emb t)    = TM.Emb $ eraseNe t
eraseNf Nat        = TM.Nat
eraseNf Set        = TM.Set

eraseNe :: Ne g -> TM.Infer g
eraseNe (Cut a sp) = case viewl $ unSpine sp of
  EmptyL -> TM.Var a
  _      -> TM.Cut (TM.Var a) $ eraseSpine sp

eraseSpine :: Spine g -> TM.Spine g
eraseSpine = TM.Spine . fmap eraseElim . unSpine

eraseElim :: Elim g -> TM.Elim g
eraseElim (App t)      = TM.App $ eraseNf t
eraseElim (Rec ty z s) = TM.Rec (eraseNf ty) (eraseNf z) (eraseNf s)

eraseBinder :: Binder g -> TM.Binder g
eraseBinder (Pi s) = TM.Pi $ eraseNf s
eraseBinder Lam    = TM.Lam

instance SContextI g => Show (Nf g) where
  show = show . eraseNf

instance SContextI g => Show (Ne g) where
  show = show . eraseNe
