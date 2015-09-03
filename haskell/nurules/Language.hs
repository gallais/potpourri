{-# OPTIONS  -Wall          #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}

module Language where

--import Data.Foldable as Fold
import Data.Sequence
import Context

----------------------------------------------------
-- THE LANGUAGE
-- We divide the language between checkable terms and inferrable
-- ones.
----------------------------------------------------

type Type (g :: Context) = Check g

data Check (g :: Context) =
    Bnd (Binder g) (Check ('Bind g))
  | Zro
  | Suc (Check g)
  | Emb (Infer g)
  | Nat
  | Set

data Infer (g :: Context) =
    Var (Var g)
  | Cut (Infer g) (Spine g)
  | Ann (Check g) (Type g)

newtype Spine (g :: Context) = Spine { unSpine :: Seq (Elim g) }

data Elim (g :: Context) =
    App (Check g)
  | Rec (Type g) (Check g) (Check g)

data Binder (g :: Context) =
    Lam
  | Pi  (Type g)
  | Let (Infer g)

instance Monoid (Spine g) where
  mempty         = Spine empty
  mappend sp sp' = Spine $ unSpine sp >< unSpine sp'

piAbs :: Type g -> Type ('Bind g) -> Type g
piAbs a = Bnd (Pi a)

lamAbs :: Check ('Bind g) -> Check g
lamAbs = Bnd Lam

letAbs :: Type g -> Check g -> Check ('Bind g) -> Check g
letAbs ty te = Bnd (Let (Ann te ty))

var :: Var g -> Check g
var = Emb . Var

appInfer :: Infer a -> Elim a -> Infer a
appInfer (Cut a sp) el = Cut a $ Spine $ unSpine sp |> el
appInfer t          el = Cut t $ Spine $ singleton el
