{-# OPTIONS  -Wall         #-}
{-# LANGUAGE DeriveFunctor #-}

module Language where

----------------------------------------------------
-- THE LANGUAGE
-- We divide the language between checkable terms and inferrable
-- ones.
----------------------------------------------------

type Type a = Check a

data Check a =
    Bnd (Binder a) (Check (Maybe a))
  | Zro
  | Suc (Check a)
  | Emb (Infer a)
  | Nat
  | Set
  deriving (Show, Functor)

data Infer a =
    Var a
  | Cut (Infer a) (Spine a)
  | Ann (Check a) (Type a)
  deriving (Show, Functor)

type Spine a = [Elim a]

data Elim a =
    App (Check a)
  | Rec (Type a) (Check a) (Check a)
  deriving (Show, Functor)

data Binder a =
    Lam
  | Pi  (Type a)
  | Let (Infer a)
  deriving (Show, Functor)

piAbs :: Type a -> Type (Maybe a) -> Type a
piAbs a = Bnd (Pi a)

lamAbs :: Check (Maybe a) -> Check a
lamAbs = Bnd Lam

letAbs :: Type a -> Check a -> Check (Maybe a) -> Check a
letAbs ty te = Bnd (Let (Ann te ty))

var :: a -> Check a
var = Emb . Var
