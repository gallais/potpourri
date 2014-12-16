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
  deriving Functor

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

appInfer :: Infer a -> Elim a -> Infer a
appInfer (Cut a sp) el = Cut a $ sp ++ [el]
appInfer t          el = Cut t $ [el]

ppCheck :: [String] -> (a -> String) -> Check a -> String
ppCheck (n : ns) vars (Bnd bd t) = ppBinder n ns vars bd ++ ' ' : ppCheck ns (maybe n vars) t
ppCheck _        _    Nat        = "Nat"
ppCheck _        _    Set        = "Set"
ppCheck _        _    Zro        = "0"
ppCheck ns       vars (Suc m)    = ppNat ns vars m 1
ppCheck ns       vars (Emb t)    = ppInfer ns vars t

ppNat :: [String] -> (a -> String) -> Check a -> Int -> String
ppNat _  _    Zro     k = show k
ppNat ns vars (Suc m) k = ppNat ns vars m (k + 1)
ppNat ns vars t       k = show k ++ " + " ++ ppCheck ns vars t

ppInfer :: [String] -> (a -> String) -> Infer a -> String
ppInfer _  vars (Var a)    = vars a
ppInfer ns vars (Cut t sp) = ppElims ns vars (ppInfer ns vars t) sp
ppInfer ns vars (Ann t ty) = '(' : ppCheck ns vars t ++ " : " ++ ppCheck ns vars ty ++ ")"

ppBinder :: String -> [String] -> (a -> String) -> Binder a -> String
ppBinder n ns vars (Pi s)  = '(' : n ++ " : " ++ ppCheck ns vars s ++ ") ->"
ppBinder n ns vars Lam     = '\\' : n ++ "."
ppBinder n ns vars (Let s) = "let " ++ n ++ " = " ++ ppInfer ns vars s ++ " in\n"

ppElims :: [String] -> (a -> String) -> String -> Spine a -> String
ppElims ns vars = foldl (ppElim ns vars)

ppElim :: [String] -> (a -> String) -> String -> Elim a -> String
ppElim ns vars t (App u)     = '(' : t ++ ") $ " ++ ppCheck ns vars u
ppElim ns vars t (Rec p z s) = "Rec[ " ++ ppCheck ns vars z ++ ", " ++ ppCheck ns vars s ++ " ] " ++ t

instance Show (Check a) where
  show = ppCheck (fmap (:[]) ['a'..'z']) undefined
