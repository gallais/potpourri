module TypeCheck where

import Data.Foldable as Fold
import Data.Sequence as Seq

import Context
import Language
import NormalForms (eraseNf)
import FancyDomain
import Equality

import Control.Monad

substCheck :: (a -> Infer b) -> Check a -> Check b
substCheck _   Set        = Set
substCheck _   Nat        = Nat
substCheck _   Zro        = Zro
substCheck sub (Suc m)    = Suc $ substCheck sub m
substCheck sub (Bnd bd t) = Bnd (substBinder sub bd) $ substCheck (sub .#~ Var Nothing) t
substCheck sub (Emb t)    = Emb $ substInfer sub t

substInfer :: (a -> Infer b) -> Infer a -> Infer b
substInfer ctx (Var a)    = ctx a
substInfer ctx (Cut t sp) = Cut (substInfer ctx t) $ fmap (substElim ctx) sp
substInfer ctx (Ann t ty) = Ann (substCheck ctx t) (substCheck ctx ty)

substElim :: (a -> Infer b) -> Elim a -> Elim b
substElim ctx (App t)     = App $ substCheck ctx t
substElim ctx (Rec t z s) = Rec (substCheck ctx t) (substCheck ctx z) (substCheck ctx s)

substBinder :: (a -> Infer b) -> Binder a -> Binder b
substBinder _   Lam     = Lam
substBinder ctx (Pi s)  = Pi $ substCheck ctx s
substBinder ctx (Let s) = Let $ substInfer ctx s

(#~) :: Functor f => (a -> f b) -> f b -> (Maybe a -> f b)
ctx #~ ty = maybe ty ctx

(.#~) :: Functor f => (a -> f b) -> f (Maybe b) -> (Maybe a -> f (Maybe b))
ctx .#~ ty = maybe ty $ fmap Just . ctx

(.#~.) :: Functor f => (a -> f b) -> f b -> (Maybe a -> f (Maybe b))
ctx .#~. ty = fmap Just . maybe ty ctx

check :: (Eq a, ValidContext a) => (a -> Type a) -> Type a -> Check a -> Maybe ()
check _   Set             Set             = return ()
check _   Set             Nat             = return ()
check ctx Set             (Bnd (Pi s) t)  = check ctx Set s >> check (ctx .#~. s) Set t
check ctx (Bnd (Pi s) t)  (Bnd Lam b)     = check (ctx .#~. s) t b
check ctx (Bnd (Let s) t) b               =
  infer ctx s >> check ctx (substCheck (Var #~ s) t) b
check _   Nat             Zro             = return ()
check ctx Nat             (Suc m)         = check ctx Nat m
check ctx ty              (Bnd (Let s) b) =
  infer ctx s >> check ctx ty (substCheck (Var #~ s) b)
check ctx ty              (Emb t)         = infer ctx t >>= guard . (ty ==)
check _ ty te = Nothing

infer :: (Eq a, ValidContext a) => (a -> Type a) -> Infer a -> Maybe (Type a)
infer ctx (Var a)    = return $ ctx a
infer ctx (Cut t sp) = infer ctx t >>= \ ty -> elims ctx ty t sp
infer ctx (Ann t ty) = check ctx ty t >> return ty

elims :: (Eq a, ValidContext a) => (a -> Type a) -> Type a -> Infer a -> Spine a -> Maybe (Type a)
elims ctx ty t = fmap fst . Fold.foldl (\ m el -> m >>= elim ctx el) (Just (eraseNf (normCheck ty), t))

elim :: (Eq a, ValidContext a) => (a -> Type a) -> Elim a -> (Type a, Infer a) -> Maybe (Type a, Infer a)
elim ctx el@(App u)     (Bnd (Pi s) t, te) =
  check ctx s u >> return (substCheck (Var #~ Ann u s) t, appInfer te el)
elim ctx el@(Rec p z s) (Nat, te)          =
  let piNatSet = Bnd (Pi Nat) Set
      indBase  = eraseNf $ normCheck $ Emb $ Cut (Ann p piNatSet) $ singleton $ App Zro
      indHypo  = eraseNf $ normCheck $
                   Bnd (Pi Nat) $ Bnd (Pi $ Emb $ Cut (Ann (fmap Just p) piNatSet)
                                                      $ singleton $ App $ var Nothing)
                                $ Emb $ Cut (Ann (fmap (Just . Just) p) piNatSet)
                                            $ singleton $ App $ Suc $ var Nothing
  in check ctx piNatSet p >>
     check ctx indBase z  >>
     check ctx indHypo s  >>
     return (eraseNf (normInfer (Cut (Ann p piNatSet) $ singleton $ App (Emb te)))
            , appInfer te el)
elim _ _ _ = Nothing
