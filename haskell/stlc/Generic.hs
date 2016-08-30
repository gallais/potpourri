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
import Control.Newtype

type (~>) (x :: k -> *) y = forall a. x a -> y a
type (~~>) (f :: (k -> *) -> (l -> *)) g = forall x y. x ~> y -> f x ~> g y

newtype Scope                (t :: * -> *) (a :: *) =
  Scope  { runScope  :: t (Maybe a) }
newtype Kripke (e :: * -> *) (v :: * -> *) (a :: *) =
  Kripke { runKripke :: forall b. (a -> b) -> e b -> v b }

kripke :: (v ~> w) -> Kripke e v a -> Kripke e w a
kripke f k = Kripke $ \ i e -> f $ runKripke k i e

instance Functor (Kripke e v) where
  fmap f e = Kripke $ \ i -> runKripke e (i . f)

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

instance Newtype (Identity v a) (v a) where
  pack   = Identity
  unpack = runIdentity

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
    L b   -> L $ fs' runIdentity $ s (over Identity) $ fs Identity b
    A f t -> A (r f) (r t)

-- Weird language with sums and "fused cases" to show that
-- a scope may span more than one sub-structures:
-- CA (LI a) (l , r) --->* l [0 <- a]
-- CA (RI a) (l , r) --->* r [0 <- a]

newtype Pair x a = Pair { runPair :: (x a, x a) }
pair :: (x a -> x' a') -> Pair x a -> Pair x' a'
pair f (Pair (t, u)) = Pair (f t, f u)

first :: Pair x a -> x a
first (Pair (l, _)) = l

second :: Pair x a -> x a
second (Pair (_, r)) = r

instance Functor x => Functor (Pair x) where
  fmap f (Pair (l, r)) = Pair (fmap f l, fmap f r)

data CsF (r :: ((* -> *) -> (* -> *)) -> (* -> *))
         (s :: (* -> *) -> (* -> *))
         (a :: *)
         :: * where
  LI :: r s a -> CsF r s a                     -- Left  Injection
  RI :: r s a -> CsF r s a                     -- Right Injection
  CA :: r s a -> s (Pair (r s)) a -> CsF r s a -- Case  Analysis
  FX :: s (r s) a -> CsF r s a                 -- Fixpoint Operator
  LA :: s (r s) a -> CsF r s a                 -- Lambda Abstraction
  AP :: Pair (r s) a -> CsF r s a              -- Application
  UN :: CsF r s a

instance SyntaxWithBinding CsF where
  reindex fs fs' r s e = case e of
    LI t   -> LI $ r t
    RI t   -> RI $ r t
    CA c b -> CA (r c) $ s pair b
    FX f   -> FX $ fs' runIdentity $ s (over Identity) $ fs Identity f
    LA b   -> LA $ fs' runIdentity $ s (over Identity) $ fs Identity b
    AP p   -> AP $ pair r p
    UN     -> UN

newtype Variable a = Variable { runVar :: a }
deriving instance Functor Variable

instance Alg TmF Variable Term where
  ret _ = Var . runVar
  alg e = case e of
    L b   -> Fix $ L $ Scope $ abstract' Variable $ kripke runConst b
    A f t -> Fix $ (A `on` runConst) f t

instance Alg TmF Term Term where
  ret _ = id
  alg e = case e of
    L b   -> Fix $ L $ Scope $ abstract' Var $ kripke runConst b
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
  Fix (L b)   -> Fix $ L $ Scope $ reifyTerm $ Model $ abstract' reflectTerm b
  Fix (A f t) -> Fix $ (A `on` reifyTerm . Model) f t

reflectTerm :: a -> Model TmF a
reflectTerm = Model . Var

instance Functor (Fix TmF (Kripke (Model f))) where
  fmap f e = case e of
    Var a       -> Var (f a)
    Fix e' -> Fix $ case e' of
      L b   -> L $ fmap f b
      A t u -> (A `on` fmap f) t u

deriving instance Functor (Model TmF)

normTerm :: Term a -> Term a
normTerm = reifyTerm . eval reflectTerm

abstract' :: (forall a. a -> e a) -> forall a. Kripke e v a -> v (Maybe a)
abstract' var k = runKripke k Just (var Nothing)

abstract :: (forall a. a -> e a) -> Kripke e (Const v r) ~> Scope v
abstract var = Scope . runConst . abstract' var

instance Alg CsF Variable Case where
  ret _ = Var . runVar
  alg e = case e of
    LI t    -> Fix $ LI $ runConst t
    RI t    -> Fix $ RI $ runConst t
    CA f kp -> Fix $ CA (runConst f) $ Scope $ pair runConst $ abstract' Variable kp
    FX f    -> Fix $ FX $ abstract Variable f
    LA b    -> Fix $ FX $ abstract Variable b
    AP p    -> Fix $ AP $ pair runConst p
    UN      -> Fix UN

instance Alg CsF Case Case where
  ret _ = id
  alg e = case e of
    LI t    -> Fix $ LI $ runConst t
    RI t    -> Fix $ RI $ runConst t
    CA f kp -> Fix $ CA (runConst f) $ Scope $ pair runConst $ runKripke kp Just (Var Nothing)
    FX kp   -> Fix $ FX $ abstract Var kp
    LA b    -> Fix $ LA $ abstract Var b
    AP p    -> Fix $ AP $ pair runConst p
    UN      -> Fix UN

instance Alg CsF (Model CsF) (Model CsF) where
  ret _ = id
  alg e =
    let cleanup = runModel . runConst
    in case e of
    LI t    -> Model $ Fix $ LI $ cleanup t
    RI t    -> Model $ Fix $ RI $ cleanup t
    CA f kp -> case cleanup f of
      Fix (LI l) -> runConst $ first  $ runKripke kp id $ Model l 
      Fix (RI r) -> runConst $ second $ runKripke kp id $ Model r
      f'          -> Model $ Fix $ CA f' $ kripke (pair cleanup) kp
    FX kp   -> fixpoint $ kripke runConst kp
    LA b    -> Model $ Fix $ LA $ kripke cleanup b
    AP p    -> case cleanup (first p) of
      Fix (LA b) -> Model $ runKripke b id (runConst $ second p)
      _          -> Model $ Fix $ AP $ pair cleanup p    
    UN      -> Model $ Fix UN      

reifyCase :: Model CsF a -> Case a
reifyCase v = case runModel v of
  Var a  -> Var a
  Fix e' -> Fix $ case e' of
    LI t    -> LI $ reifyCase $ Model t
    RI t    -> RI $ reifyCase $ Model t
    CA f kp -> CA (reifyCase $ Model f) $ Scope $ pair (reifyCase . Model) $ abstract' (Model . Var) kp
    FX kp   -> FX $ Scope $ reifyCase $ Model $ abstract' (Model . Var) kp
    LA kp   -> LA $ Scope $ reifyCase $ Model $ abstract' (Model . Var) kp
    AP p    -> AP $ pair (reifyCase . Model) p
    UN      -> UN

instance Functor (Fix CsF (Kripke (Model CsF))) where
  fmap f e = case e of
    Var a  -> Var $ f a
    Fix e' -> Fix $ case e' of
      LI t    -> LI $ fmap f t
      RI t    -> RI $ fmap f t
      CA t kp -> CA (fmap f t) $ fmap f kp
      FX kp   -> FX $ fmap f kp
      LA kp   -> LA $ fmap f kp
      AP p    -> AP $ fmap f p
      UN      -> UN

deriving instance Functor (Model CsF)

reflectCase :: a -> Model CsF a
reflectCase = Model . Var

normCase :: Case a -> Case a
normCase = reifyCase . eval reflectCase

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

natToCase :: Integer -> Case a
natToCase n | n <= 0 = Fix $ LI $ Fix UN
natToCase n          = Fix $ RI $ natToCase (n - 1)

caseToNat :: Case a -> Integer
caseToNat t = case t of
  Fix (LI (Fix UN)) -> 0
  Fix (RI n)        -> 1 + caseToNat n
  _                 -> error "Malformed Nat"

fixpoint :: Kripke v v a -> v a
fixpoint kp = runKripke kp id (fixpoint kp)

plus :: Case Void
plus =
  Fix $ LA               $ Scope $ {- m  -}
  Fix $ FX               $ Scope $ {- m+ -}
  Fix $ LA               $ Scope $ {- n  -}
  Fix $ CA (Var Nothing) $ Scope $ {- case n -}
  Pair
  ( Var (Just (Just (Just Nothing)))
  , Fix (RI $ Fix $ AP $ Pair (Var (Just (Just Nothing)), Var Nothing))
  )

plus' :: Case Void -> Case Void -> Case Void
plus' m n = Fix $ AP $ Pair (Fix (AP (Pair (plus, m))),n)

five :: Integer
five = caseToNat $ normCase $ (plus' `on` natToCase) 2 3
