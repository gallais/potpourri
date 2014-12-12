{-# OPTIONS  -Wall         #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes    #-}

module FancyDomain where

import Context
import Language

----------------------------------------------------
-- THE EVALUATION DOMAIN
-- We opt for a well-scoped by construction approach which lets us
-- avoid the back-and-forth motion bewteen de Bruijn levels / indices
-- typical of name generation-based approaches.
-- This is made possible by the typical Kripke structure of the BND
-- construct taking into account all possible future extensions of
-- the current scope.
----------------------------------------------------

data Dom a =
    NF (ActDom a)
  | NE a [ArgDom a] -- This is a very crude approximation
                    -- It is convenient to have spines to implement cut
                    -- but we would like to be able to pattern-match on
                    -- the right hand side in order to implement nu-rules
                    -- easily
  | BT
  deriving Functor

data ArgDom a =
    APP (Dom a)
  | REC (Dom a) (Dom a) (Dom a)
  deriving Functor

data ActDom a =
    BND (BndDom a) (forall b. (a -> b) -> Dom b -> Dom b)
  | SUC (Dom a)
  | ZRO
  | NAT
  | SET
  deriving Functor

data BndDom a = LAM | PI (Dom a)
  deriving Functor

-- The evaluation functions

evalScope :: Check (Maybe a) -> (a -> Dom b) -> forall c. (b -> c) -> Dom c -> Dom c
evalScope t rho wk d = evalCheck t $ maybe d $ fmap (fmap wk) rho

evalBinder :: Binder a -> Check (Maybe a) -> (a -> Dom b) -> Dom b
evalBinder Lam     t rho = NF $ BND LAM                    $ evalScope t rho
evalBinder (Pi s)  t rho = NF $ BND (PI $ evalCheck s rho) $ evalScope t rho
evalBinder (Let u) t rho = evalCheck t $ maybe (evalInfer u rho) rho

evalCheck :: Check a -> (a -> Dom b) -> Dom b
evalCheck (Bnd bd t) rho = evalBinder bd t rho
evalCheck Zro        _   = NF ZRO
evalCheck (Suc n)    rho = NF $ SUC $ evalCheck n rho
evalCheck (Emb t)    rho = evalInfer t rho
evalCheck Nat        _   = NF NAT
evalCheck Set        _   = NF SET

evalInfer :: Infer a -> (a -> Dom b) -> Dom b
evalInfer (Var a)    rho = rho a
evalInfer (Ann t _)  rho = evalCheck t rho
evalInfer (Cut t sp) rho = cut (evalInfer t rho) $ fmap (flip evalElim rho) sp

evalElim :: Elim a -> (a -> Dom b) -> ArgDom b
evalElim (App t)      rho = APP $ evalCheck t rho
evalElim (Rec ty z s) rho = REC (evalCheck ty rho) (evalCheck z rho) (evalCheck s rho)

cut :: Dom a -> [ArgDom a] -> Dom a
cut d         []                = d
cut BT        _                 = BT
cut (NE a sp) args              = NE a $ sp ++ args
cut d         (APP u      : tl) = cut (app d u) tl
cut d         (REC ty z s : tl) = cut (rec ty z s d) tl

app :: Dom a -> Dom a -> Dom a
app (NF (BND _ d)) u = d id u
app (NE a sp)      u = NE a $ sp ++ [APP u]
app _              _ = BT

rec :: Dom a -> Dom a -> Dom a -> Dom a -> Dom a
rec _  z _ (NF ZRO)     = z
rec ty z s (NF (SUC d)) = s `app` d `app` rec ty z s d
rec ty z s (NE a sp)    = NE a $ sp ++ [REC ty z s]
rec _  _ _ _            = BT


----------------------------------------------------
-- THE REIFICATION PROCESS
----------------------------------------------------

reflect :: a -> Dom a
reflect a = NE a []

reify :: Dom a -> Check a
reify (NF d)    = reifyAct d
reify (NE a []) = Emb $ Var a
reify (NE a sp) = Emb $ Cut (Var a) $ fmap reifyArg sp

reifyAct :: ActDom a -> Check a
reifyAct (BND LAM    d) = lamAbs          $ reify $ d Just $ reflect Nothing
reifyAct (BND (PI s) d) = piAbs (reify s) $ reify $ d Just $ reflect Nothing
reifyAct (SUC d)        = Suc $ reify d
reifyAct ZRO            = Zro
reifyAct NAT            = Nat
reifyAct SET            = Set

reifyArg :: ArgDom a -> Elim a
reifyArg (APP t)      = App $ reify t
reifyArg (REC ty z s) = Rec (reify ty) (reify z) (reify s)

instance Show a => Show (Dom a) where
  show d = show $ reify d

norm :: ValidContext a => Check a -> Check a
norm t = reify $ evalCheck t $ diag (reflect Nothing)
