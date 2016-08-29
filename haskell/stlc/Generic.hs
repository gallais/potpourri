{-# OPTIONS -Wall                  #-}
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
{-# LANGUAGE ImpredicativeTypes    #-}

module Generic where

import GHC.TypeLits
import Data.Void
import Data.Function
import Data.Functor.Classes
import Data.Proxy


type (~>) (x :: k -> *) y = forall a. x a -> y a
type (~~>) (f :: (k -> *) -> (l -> *)) g = forall x y. x ~> y -> f x ~> g y

newtype Scope                (t :: * -> *) (a :: *) =
  Scope  { runScope  :: t (Maybe a) }
newtype Kripke (e :: * -> *) (v :: * -> *) (a :: *) =
  Kripke { runKripke :: forall b. (a -> b) -> e b -> v b }

kripke :: (v ~> w) -> Kripke e v a -> Kripke e w a
kripke f k = Kripke $ \ i e -> f $ runKripke k i e

instance Show1 t => Show1 (Scope t) where
  showsPrec1 i (Scope t) = showString "Scope { runScope = "
                         . showsPrec1 i t
                         . showString " }"
instance (Show a, Show1 t) => Show (Scope t a) where showsPrec = showsPrec1

class Eval t e v where eval :: (a -> e b) -> t a -> v b
class Alg  t e v where
  alg  :: t (Const v) (Kripke e) a -> v a
  ret  :: Proxy t -> e ~> v

-- This is what I'd like to write:
-- kind Scoped  = * -> *
-- kind ScopedT = Scoped -> Scoped
-- kind Syntax  = ScopedT -> Scoped
-- kind SyntaxT = Syntax -> Syntax
-- class SyntaxWithBinding (syn :: SyntaxT) where

class SyntaxWithBinding (syn :: (((* -> *) -> (* -> *)) -> * -> *) -> ((* -> *) -> * -> *) -> * -> *) where
  reindex :: (scp ~~> scp)
          -> (scp' ~~> scp')
          -- Reindexing properties
          -> (rec scp a -> rec' scp' a')
          -> (forall f. (forall b b'. (rec scp b -> rec' scp' b') -> f (rec scp) b -> f (rec' scp') b') -> scp (f (rec scp)) a -> scp' (f (rec' scp')) a')
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

newtype Const    (v :: k -> *) (i :: l) (a :: k) = Const    { runConst :: v a }
newtype Identity (v :: k -> *)          (a :: k) = Identity { runIdentity :: v a }

instance (Functor e, SyntaxWithBinding t, Alg t e v) => Eval (Fix t Scope) e v where
  eval = go where

    go :: forall a b. (a -> e b) -> Fix t Scope a -> v b
    go rho (Var a) = ret (Proxy :: Proxy t) $ rho a
    go rho (Fix t) = alg $ reindex (\ f -> Scope . f . runScope)
                                   (\ f k -> Kripke $ \ i e -> f $ runKripke k i e)
                                   (Const . go rho)
                                   (\ g b -> Kripke $ \ i e -> g (Const . go (maybe e (fmap i . rho))) $ runScope b)
                                   t


data TmF (r :: ((* -> *) -> (* -> *)) -> (* -> *))
         (s :: (* -> *) -> (* -> *))
         (a :: *)
         :: * where
  L :: s (r s) a      -> TmF r s a
  A :: r s a -> r s a -> TmF r s a

instance (Show1 (r s), Show1 (s (r s))) => Show1 (TmF r s) where
  showsPrec1 i e = case e of
    L b   -> showString "L " . showsPrec1 (1+i) b
    A f t -> showsBinary1 "A" i f t

deriving instance (Show (r s a), Show (s (r s) a)) => Show (TmF r s a)
deriving instance (Functor (r s), Functor (s (r s))) => Functor (TmF r s)

instance SyntaxWithBinding TmF where
  reindex fs fs' r s e = case e of
    L b   -> L $ fs' runIdentity $ s (\ f -> Identity . f . runIdentity) $ fs Identity b
    A f t -> A (r f) (r t)

-- Weird language with sums and "fused cases" to show that
-- a scope may span more than one sub-structures:
-- CA (LI a) (l , r) --->* l [0 <- a]
-- CA (RI a) (l , r) --->* r [0 <- a]

newtype Pair x a = Pair { runPair :: (x a, x a) }
pair :: (x a -> x' a') -> Pair x a -> Pair x' a'
pair f (Pair (t, u)) = Pair (f t, f u)


data CsF (r :: ((* -> *) -> (* -> *)) -> (* -> *))
         (s :: (* -> *) -> (* -> *))
         (a :: *)
         :: * where
  LI :: r s a -> CsF r s a                     -- Left  Injection
  RI :: r s a -> CsF r s a                     -- Right Injection
  CA :: r s a -> s (Pair (r s)) a -> CsF r s a -- Case  Analysis

instance SyntaxWithBinding CsF where
  reindex _ _ r s e = case e of
    LI t   -> LI $ r t
    RI t   -> RI $ r t
    CA c b -> CA (r c) $ s pair b

newtype Variable a = Variable { runVar :: a }
deriving instance Functor Variable

instance Alg TmF Variable Term where
  ret _ = Var . runVar
  alg e = case e of
    L b   -> Fix $ L $ Scope $ abstract Variable $ kripke runConst b
    A f t -> Fix $ (A `on` runConst) f t

instance Alg TmF Term Term where
  ret _ = id
  alg e = case e of
    L b   -> Fix $ L $ Scope $ abstract Var $ kripke runConst b
    A f t -> Fix $ (A `on` runConst) f t

newtype Model f a = Model { runModel :: Fix f (Kripke (Model f)) a }

instance Alg TmF (Model TmF) (Model TmF) where
  ret _ = id
  alg e = case e of
    L b   -> Model $ Fix $ L $ kripke (runModel . runConst) b
    A f t -> case runModel (runConst t) of
      Fix (L b) -> Model $ runKripke b id (runConst t)
      _         -> Model $ Fix $ (A `on` runModel . runConst) f t

reifyTerm :: Model TmF a -> Term a
reifyTerm m = case runModel m of
  Var a       -> Var a
  Fix (L b)   -> Fix $ L $ Scope $ reifyTerm $ Model $ abstract reflectTerm b
  Fix (A f t) -> Fix $ (A `on` reifyTerm . Model) f t

reflectTerm :: a -> Model TmF a
reflectTerm = Model . Var

instance Functor (Fix TmF (Kripke (Model f))) where
  fmap f e = case e of
    Var a       -> Var (f a)
    Fix (L b)   -> Fix $ L $ Kripke $ \ i -> runKripke b (i . f)
    Fix (A t u) -> Fix $ (A `on` fmap f) t u

deriving instance Functor (Model TmF)

normTerm :: Term a -> Term a
normTerm = reifyTerm . eval reflectTerm

abstract :: (forall a. a -> e a) -> forall a. Kripke e v a -> v (Maybe a)
abstract var k = runKripke k Just (var Nothing)

instance Alg CsF Variable Case where
  ret _ = Var . runVar
  alg e = case e of
    LI t    -> Fix $ LI $ runConst t
    RI t    -> Fix $ RI $ runConst t
    CA f kp -> Fix $ CA (runConst f) $ Scope $ pair runConst $ runKripke kp Just (Variable Nothing)

instance Alg CsF Case Case where
  ret _ = id
  alg e = case e of
    LI t    -> Fix $ LI $ runConst t
    RI t    -> Fix $ RI $ runConst t
    CA f kp -> Fix $ CA (runConst f) $ Scope $ pair runConst $ runKripke kp Just (Var Nothing)

type Case = Fix CsF Scope
type Term = Fix TmF Scope

renameTerm :: Term a -> (a -> b) -> Term b
renameTerm = flip $ eval . (Variable .)

renameCase :: Case a -> (a -> b) -> Case b
renameCase = flip $ eval . (Variable .)

instance Functor (Fix TmF Scope) where fmap = flip renameTerm
instance Functor (Fix CsF Scope) where fmap = flip renameCase

substTerm :: Term a -> (a -> Term b) -> Term b
substTerm = flip eval 

substCase :: Case a -> (a -> Case b) -> Case b
substCase = flip eval 

type family Free (n :: Nat) :: * where
  Free 0 = Void
  Free n = Maybe (Free (n - 1))

type OCase n = Case (Free n)
type OTerm n = Term (Free n)

oCASE :: OCase 1
oCASE = Fix $ CA (Var Nothing) $ Scope $ Pair (Var (Just Nothing), Var Nothing)

oCASE' :: OCase 4
oCASE' = renameCase oCASE $ Just . Just . Just

oTERM :: OTerm 1
oTERM = Fix $ L $ Scope $ Var $ Just Nothing

oTERM' :: OTerm 2
oTERM' = renameTerm oTERM Just

idTERM :: Term Void
idTERM = Fix $ L $ Scope $ Var Nothing

falseTERM :: Term Void
falseTERM = substTerm oTERM $ maybe idTERM absurd

cutTERM :: Term Void
cutTERM = Fix $ A falseTERM falseTERM -- (\ x y -> y) (\ x y -> y) ---->* (\ y -> y)

normTERM :: Term Void
normTERM = normTerm cutTERM

