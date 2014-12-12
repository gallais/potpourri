{-# OPTIONS  -Wall         #-}
{-# LANGUAGE DeriveFunctor #-}

module NormalForms where

import qualified Language as TM

type Type a = Nf a

data Nf a =
    Bnd (Binder a) (Nf (Maybe a))
  | Zro
  | Suc (Nf a)
  | Emb (Ne a)
  | Nat
  | Set
  deriving (Show, Functor)

data Ne a =
    Var a
  | Cut a (Spine a)
  deriving (Show, Functor)

type Spine a = [Elim a]

data Elim a =
    App (Nf a)
  | Rec (Type a) (Nf a) (Nf a)
  deriving (Show, Functor)

data Binder a =
    Lam
  | Pi  (Type a)
  deriving (Show, Functor)

piAbs :: Type a -> Type (Maybe a) -> Type a
piAbs a = Bnd (Pi a)

lamAbs :: Nf (Maybe a) -> Nf a
lamAbs = Bnd Lam


-- Normal forms are a subset of the language, obviously
eraseNf :: Nf a -> TM.Check a
eraseNf (Bnd bnd t) = TM.Bnd (eraseBinder bnd) (eraseNf t)
eraseNf Zro         = TM.Zro
eraseNf (Suc m)     = TM.Suc $ eraseNf m
eraseNf (Emb t)     = TM.Emb $ eraseNe t
eraseNf Nat         = TM.Nat
eraseNf Set         = TM.Set

eraseNe :: Ne a -> TM.Infer a
eraseNe (Var a)    = TM.Var a
eraseNe (Cut a sp) = TM.Cut (TM.Var a) $ eraseSpine sp

eraseSpine :: Spine a -> TM.Spine a
eraseSpine = fmap eraseElim

eraseElim :: Elim a -> TM.Elim a
eraseElim (App t)      = TM.App $ eraseNf t
eraseElim (Rec ty z s) = TM.Rec (eraseNf ty) (eraseNf z) (eraseNf s)

eraseBinder :: Binder a -> TM.Binder a
eraseBinder (Pi s) = TM.Pi $ eraseNf s
eraseBinder Lam    = TM.Lam
