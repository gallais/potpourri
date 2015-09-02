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

piAbs :: Type g -> Type ('Bind g) -> Type g
piAbs a = Bnd (Pi a)

lamAbs :: Check ('Bind g) -> Check g
lamAbs = Bnd Lam

letAbs :: Type g -> Check g -> Check ('Bind g) -> Check g
letAbs ty te = Bnd (Let (Ann te ty))

--var :: Var g -> Check g
--var = Emb . Var

appInfer :: Infer a -> Elim a -> Infer a
appInfer (Cut a sp) el = Cut a $ Spine $ unSpine sp |> el
appInfer t          el = Cut t $ Spine $ singleton el

{-
ppCheck :: [String] -> (a -> String) -> Check g -> String
ppCheck (n : ns) vars (Bnd bd t) = ppBinder n ns vars bd ++ ' ' : ppCheck ns (maybe n vars) t
ppCheck _        _    Nat        = "Nat"
ppCheck _        _    Set        = "Set"
ppCheck _        _    Zro        = "0"
ppCheck ns       vars (Suc m)    = ppNat ns vars m 1
ppCheck ns       vars (Emb t)    = ppInfer ns vars t

ppNat :: [String] -> (a -> String) -> Check g -> Int -> String
ppNat _  _    Zro     k = show k
ppNat ns vars (Suc m) k = ppNat ns vars m (k + 1)
ppNat ns vars t       k = show k ++ " + " ++ ppCheck ns vars t

ppInfer :: [String] -> (a -> String) -> Infer a -> String
ppInfer _  vars (Var a)    = vars a
ppInfer ns vars (Cut t sp) = ppElims ns vars (ppInfer ns vars t) sp
ppInfer ns vars (Ann t ty) = '(' : ppCheck ns vars t ++ " : " ++ ppCheck ns vars ty ++ ")"

ppBinder :: String -> [String] -> (a -> String) -> Binder a -> String
ppBinder n ns vars (Pi s)  = '(' : n ++ " : " ++ ppCheck ns vars s ++ ") ->"
ppBinder n _  _    Lam     = '\\' : n ++ "."
ppBinder n ns vars (Let s) = "let " ++ n ++ " = " ++ ppInfer ns vars s ++ " in\n"

ppElims :: [String] -> (a -> String) -> String -> Spine a -> String
ppElims ns vars = Fold.foldl (ppElim ns vars)

ppElim :: [String] -> (a -> String) -> String -> Elim a -> String
ppElim ns vars t (App u)     = '(' : t ++ ") $ " ++ ppCheck ns vars u
ppElim ns vars t (Rec _ z s) = "Rec[ " ++ ppCheck ns vars z ++ ", " ++ ppCheck ns vars s ++ " ] " ++ t

instance ValidContext a => Show (Check g) where
  show t =
    let (ns, vars) = freshNames witness $ fmap (:[]) ['a'..'z'] in
    ppCheck ns vars t
-}
