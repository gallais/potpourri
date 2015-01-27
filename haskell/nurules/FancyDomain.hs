{-# OPTIONS  -Wall         #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes    #-}

module FancyDomain where

import Data.Sequence as Seq

import Context
import qualified Language    as TM
import qualified NormalForms as NF

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
  | NE a (Seq (ArgDom a))
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

evalScope :: TM.Check (Maybe a) -> (a -> Dom b) -> forall c. (b -> c) -> Dom c -> Dom c
evalScope t rho wk d = evalCheck t $ maybe d $ fmap (fmap wk) rho

evalBinder :: TM.Binder a -> TM.Check (Maybe a) -> (a -> Dom b) -> Dom b
evalBinder TM.Lam     t rho = NF $ BND LAM                    $ evalScope t rho
evalBinder (TM.Pi s)  t rho = NF $ BND (PI $ evalCheck s rho) $ evalScope t rho
evalBinder (TM.Let u) t rho = evalCheck t $ maybe (evalInfer u rho) rho

evalCheck :: TM.Check a -> (a -> Dom b) -> Dom b
evalCheck (TM.Bnd bd t) rho = evalBinder bd t rho
evalCheck TM.Zro        _   = NF ZRO
evalCheck (TM.Suc n)    rho = NF $ SUC $ evalCheck n rho
evalCheck (TM.Emb t)    rho = evalInfer t rho
evalCheck TM.Nat        _   = NF NAT
evalCheck TM.Set        _   = NF SET

evalInfer :: TM.Infer a -> (a -> Dom b) -> Dom b
evalInfer (TM.Var a)    rho = rho a
evalInfer (TM.Ann t _)  rho = evalCheck t rho
evalInfer (TM.Cut t sp) rho = cut (evalInfer t rho) $ fmap (flip evalElim rho) sp

evalElim :: TM.Elim a -> (a -> Dom b) -> ArgDom b
evalElim (TM.App t)      rho = APP $ evalCheck t rho
evalElim (TM.Rec ty z s) rho = REC (evalCheck ty rho) (evalCheck z rho) (evalCheck s rho)

cut :: Dom a -> Seq (ArgDom a) -> Dom a
cut BT        _    = BT
cut (NE a sp) args = NE a $ sp >< args
cut d         args =
  case viewl args of
    EmptyL             -> d
    (APP u :< tl)      -> cut (app d u) tl
    (REC ty z s :< tl) -> cut (rec ty z s d) tl

app :: Dom a -> Dom a -> Dom a
app (NF (BND _ d)) u = d id u
app (NE a sp)      u = NE a $ sp |> APP u
app _              _ = BT

rec :: Dom a -> Dom a -> Dom a -> Dom a -> Dom a
rec _  z _ (NF ZRO)     = z
rec ty z s (NF (SUC d)) = s `app` d `app` rec ty z s d
rec ty z s (NE a sp)    = NE a $ sp |> REC ty z s
rec _  _ _ _            = BT


----------------------------------------------------
-- THE REIFICATION PROCESS
----------------------------------------------------

reflect :: a -> Dom a
reflect a = NE a empty

reify :: Dom a -> NF.Nf a
reify (NF d) = reifyAct d
reify (NE a sp)
  | Seq.null sp = NF.Emb $ NF.Var a
  | otherwise   = NF.Emb $ NF.Cut a $ fmap reifyArg sp

reifyAct :: ActDom a -> NF.Nf a
reifyAct (BND LAM    d) = NF.lamAbs          $ reify $ d Just $ reflect Nothing
reifyAct (BND (PI s) d) = NF.piAbs (reify s) $ reify $ d Just $ reflect Nothing
reifyAct (SUC d)        = NF.Suc $ reify d
reifyAct ZRO            = NF.Zro
reifyAct NAT            = NF.Nat
reifyAct SET            = NF.Set

reifyArg :: ArgDom a -> NF.Elim a
reifyArg (APP t)      = NF.App $ reify t
reifyArg (REC ty z s) = NF.Rec (reify ty) (reify z) (reify s)

instance (ValidContext a, Show a) => Show (Dom a) where
  show d = show $ reify d


normInfer :: ValidContext a => TM.Infer a -> NF.Nf a
normInfer t = reify $ evalInfer t $ diag (reflect Nothing)

normCheck :: ValidContext a => TM.Check a -> NF.Nf a
normCheck t = reify $ evalCheck t $ diag (reflect Nothing)
