{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE TypeOperators         #-}

module Generic where

-- import Data.Proxy

type (~>) (x :: k -> *) y = forall a. x a -> y a

newtype Scope                (t :: * -> *) (a :: *) =
  Scope  { runScope  :: t (Maybe a) }
newtype Kripke (e :: * -> *) (v :: * -> *) (a :: *) =
  Kripke { runKripke :: forall b. (a -> b) -> e b -> v b }


class Eval t e v where eval :: (a -> e b) -> t a -> v b
class Alg  t e v where alg  :: t (Const v) (Kripke e) a -> v a

class SyntaxWithBinding (syn :: (((* -> *) -> (* -> *)) -> * -> *) -> ((* -> *) -> * -> *) -> * -> *) where
  rewrite :: (rec scp ~> rec' scp')
          -> (forall f f'. f ~> f' -> scp f ~> scp' f')
          -> syn rec scp a -> syn rec' scp' a

instance (Functor e, Eval t e v) => Eval (Scope t) e (Kripke e v) where
  eval rho t = Kripke $ \ f e -> eval (maybe e (fmap f . rho)) $ runScope t

instance Functor t => Functor (Scope t) where
  fmap f = Scope . fmap (fmap f) . runScope

newtype Fix f (s :: (* -> *) -> (* -> *)) a = Fix { runFix :: f (Fix f) s a }

deriving instance Functor (f (Fix f) s) => Functor (Fix f s)

newtype Const (v :: * -> *) (i :: k) (a :: *) = Const { runConst :: v a }

instance (Eval (t (Fix t) Scope) e (t (Const v) (Kripke e)), Alg t e v) => Eval (Fix t Scope) e v where
  eval :: forall a b. (a -> e b) -> Fix t Scope a -> v b
  eval rho t = alg $ (eval rho (runFix t) :: t (Const v) (Kripke e) b)


newtype Var a = Var { runVar :: a }


data TmF (r :: ((* -> *) -> (* -> *)) -> (* -> *))
         (s :: (* -> *) -> (* -> *))
         (a :: *)
         :: * where
  V :: a              -> TmF r s a
  L :: s (r s) a      -> TmF r s a
  A :: r s a -> r s a -> TmF r s a

deriving instance (Functor (r s), Functor (s (r s))) => Functor (TmF r s)


instance SyntaxWithBinding TmF where
  rewrite r s t = case t of
    V a   -> V a
    L b   -> L $ s r b
    A f t -> A (r f) (r t)

{-
type Term = Fix TmF Scope

{-
rename :: Term a -> (a -> Var b) -> Term b
rename = flip eval
-}
-}
