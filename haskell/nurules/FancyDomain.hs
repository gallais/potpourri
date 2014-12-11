{-# OPTIONS  -Wall         #-}
{-# LANGUAGE DeriveFunctor #-}

module FancyDomain where

import Data.Void

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


----------------------------------------------------
-- THE EVALUATION DOMAIN
----------------------------------------------------

data Dom =
    NF ActDom
  | NE Int [ArgDom] -- This is a very crude approximation
                    -- It is convenient to have spines to implement cut
                    -- but we would like to be able to pattern-match on
                    -- the right hand side in order to implement nu-rules
                    -- easily
  | BT

data ArgDom =
    APP Dom
  | REC Dom Dom Dom

data ActDom =
    LAM (Dom -> Dom)
  | SUC Dom
  | ZRO
  | NAT
  | SET

-- The evaluation functions

evalBinder :: Binder a -> Check (Maybe a) -> (a -> Dom) -> Dom
evalBinder Lam     t rho = NF $ LAM $ \ d -> evalCheck t (maybe d rho)
evalBinder (Pi _)  t rho = NF $ LAM $ \ d -> evalCheck t (maybe d rho)
evalBinder (Let u) t rho = evalCheck t (maybe (evalInfer u rho) rho)

evalCheck :: Check a -> (a -> Dom) -> Dom
evalCheck (Bnd bd t) rho = evalBinder bd t rho
evalCheck Zro        _   = NF ZRO
evalCheck (Suc ns)    rho = NF $ SUC $ evalCheck ns rho
evalCheck (Emb t)    rho = evalInfer t rho
evalCheck Nat        _   = NF NAT
evalCheck Set        _   = NF SET

evalInfer :: Infer a -> (a -> Dom) -> Dom
evalInfer (Var a)    rho = rho a
evalInfer (Ann t _)  rho = evalCheck t rho
evalInfer (Cut t sp) rho = cut (evalInfer t rho) $ fmap (\ el -> evalElim el rho) sp

evalElim :: Elim a -> (a -> Dom) -> ArgDom
evalElim (App t)      rho = APP $ evalCheck t rho
evalElim (Rec ty z s) rho = REC (evalCheck ty rho) (evalCheck z rho) (evalCheck s rho)

cut :: Dom -> [ArgDom] -> Dom
cut d         []                = d
cut BT        _                 = BT
cut (NE a sp) args              = NE a $ sp ++ args
cut d         (APP u      : tl) = cut (app d u) tl
cut d         (REC ty z s : tl) = cut (rec ty z s d) tl

app :: Dom -> Dom -> Dom
app (NF (LAM d)) u = d u
app (NE a sp)    u = NE a $ sp ++ [APP u]
app _            _ = BT

rec :: Dom -> Dom -> Dom -> Dom -> Dom
rec _  z _ (NF ZRO)     = z
rec ty z s (NF (SUC d)) = s `app` d `app` rec ty z s d
rec ty z s (NE a sp)    = NE a $ sp ++ [REC ty z s]
rec _  _ _ _            = BT



----------------------------------------------------
-- THE REIFICATION PROCESS
-- We turn de Bruijn levels into type-level de Bruijn indices
-- thanks to a Name Index (ni) mapping already used levels to
-- the corresponding index and a Name Supply (ns) providing us
-- fresh names
----------------------------------------------------

reflect :: Int -> Dom
reflect ns = NE ns []

reify :: Dom -> (Int -> a) -> (Int -> Check a)
reify (NF d)    ni ns = reifyAct d ni ns
reify (NE a sp) ni ns = Emb $ Cut (Var $ ni a) $ fmap (\ arg -> reifyArg arg ni ns) sp

extend :: (Int -> a) -> Int -> (Int -> Maybe a)
extend ni ns m = if ns == m then Nothing else Just (ni m)

reifyAct :: ActDom -> (Int -> a) -> (Int -> Check a)
reifyAct (LAM d) ni ns = lamAbs $ reify (d $ reflect ns) (extend ni ns) $ ns + 1
reifyAct (SUC d) ni ns = Suc $ reify d ni ns
reifyAct ZRO     _  _ = Zro
reifyAct NAT     _  _ = Nat
reifyAct SET     _  _ = Set

reifyArg :: ArgDom -> (Int -> a) -> (Int -> Elim a)
reifyArg (APP t)      ni ns = App $ reify t ni ns
reifyArg (REC ty z s) ni ns = Rec (reify ty ni ns) (reify z ni ns) (reify s ni ns)

instance Show Dom where
  show d = show $ reify d (const ()) 0

norm :: Check Void -> Check Void
norm t = reify (evalCheck t absurd) undefined 0


-- examples!

plus :: Check a
plus =
  lamAbs {- m -} $
  lamAbs {- ns -} $
    Emb $ Cut (Var $ Just Nothing) $
    [ Rec (piAbs Nat Nat) (var Nothing) (lamAbs $ lamAbs $ Suc $ var Nothing) ]

four :: Check Void
four = Emb $ Cut (Ann plus (piAbs Nat $ piAbs Nat $ Nat)) $ [ App two , App two ]
  where two = Suc $ Suc Zro

main :: IO ()
main = do
  print four
  putStrLn "reduces to..."
  print $ norm four

