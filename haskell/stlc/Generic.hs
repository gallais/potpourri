{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
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
{-# LANGUAGE TypeFamilies          #-}

module Generic where

import GHC.TypeLits
import Data.Functor.Classes
import Data.Proxy

type (~>) (x :: k -> *) y = forall a. x a -> y a
type (~~>) (f :: (k -> *) -> (l -> *)) g = forall x y. x ~> y -> f x ~> g y

newtype Scope                (t :: * -> *) (a :: *) =
  Scope  { runScope  :: t (Maybe a) }
newtype Kripke (e :: * -> *) (v :: * -> *) (a :: *) =
  Kripke { runKripke :: forall b. (a -> b) -> e b -> v b }

instance Show1 t => Show1 (Scope t) where
  showsPrec1 i (Scope t) = showString "Scope { runScope = "
                         . showsPrec1 i t
                         . showString " }"
instance (Show a, Show1 t) => Show (Scope t a) where showsPrec = showsPrec1

class Eval t e v where eval :: (a -> e b) -> t a -> v b
class Alg  t e v where
  alg  :: t (Const v) (Kripke e) a -> v a
  ret  :: Proxy t -> e ~> v

class SyntaxWithBinding (syn :: (((* -> *) -> (* -> *)) -> * -> *) -> ((* -> *) -> * -> *) -> * -> *) where
  reindex :: (rec scp a -> rec' scp' a')
          -> (scp (rec scp) a -> scp' (rec' scp') a')
          -> syn rec scp a -> syn rec' scp' a'

instance (Functor e, Eval t e v) => Eval (Scope t) e (Kripke e v) where
  eval rho t = Kripke $ \ f e -> eval (maybe e (fmap f . rho)) $ runScope t


data Fix f (s :: (* -> *) -> (* -> *)) (a :: *) :: * where
   Var :: a             -> Fix f s a
   Fix :: f (Fix f) s a -> Fix f s a

instance Show1 (f (Fix f) s) => Show1 (Fix f s) where
  showsPrec1 i e = case e of
    Var v -> showString "Var " . showsPrec (1+i) v
    Fix t -> showString "Fix " . showsPrec1 (1+i) t

deriving instance (Show a, Show (f (Fix f) s a)) => Show (Fix f s a)
deriving instance Functor (f (Fix f) s) => Functor (Fix f s)

newtype Const (v :: * -> *) (i :: k) (a :: *) = Const { runConst :: v a }

instance (Functor e, SyntaxWithBinding t, Alg t e v) => Eval (Fix t Scope) e v where
  eval rho = go where

    go (Var a) = ret (Proxy :: Proxy t) $ rho a
    go (Fix t) = alg $ reindex (Const . go) (patch . eval rho) t where

    patch :: forall a. Kripke e v a -> Kripke e (Const v (Kripke e)) a
    patch (Kripke t) = Kripke $ \ i e -> Const $ t i e


data TmF (r :: ((* -> *) -> (* -> *)) -> (* -> *))
         (s :: (* -> *) -> (* -> *))
         (a :: *)
         :: * where
  L :: s (r s) a      -> TmF r s a
  A :: r s a -> r s a -> TmF r s a

instance (Show1 (r s), Show1 (s (r s))) => Show1 (TmF r s) where
  showsPrec1 i t = case t of
    L b   -> showString "L " . showsPrec1 (1+i) b
    A f t -> showsBinary1 "A" i f t

deriving instance (Show (r s a), Show (s (r s) a)) => Show (TmF r s a)
deriving instance (Functor (r s), Functor (s (r s))) => Functor (TmF r s)

instance SyntaxWithBinding TmF where
  reindex r s t = case t of
    L b   -> L $ s b
    A f t -> A (r f) (r t)

newtype Variable a = Variable { runVar :: a }
deriving instance Functor Variable

instance Alg TmF Variable Term where
  ret _ = Var . runVar
  alg t = case t of
    L b   -> Fix $ L $ Scope $ runConst $ runKripke b Just (Variable Nothing)
    A f t -> Fix $ A (runConst f) (runConst t)

type Term = Fix TmF Scope

rename :: Term a -> (a -> b) -> Term b
rename = flip $ eval . (Variable .)

type family Free (n :: Nat) :: * where
  Free 0 = ()
  Free n = Maybe (Free (n - 1))

type OTerm n = Term (Free n)

example :: OTerm 1
example = Fix $ L $ Scope $ Var $ Just Nothing

example' :: OTerm 2
example' = rename example Just
