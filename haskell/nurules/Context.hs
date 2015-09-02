{-# OPTIONS  -Wall               #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Context where

----------------------------------------------------
-- CONTEXTS
----------------------------------------------------

-- This is basically a version of `Nat` with different names
-- to match our intuition of what a context is. We can generate
-- singletons using a typeclass mechanism.

data Context = Null | Bind Context
data SContext (g :: Context) where
  SNull ::               SContext 'Null
  SBind :: SContext g -> SContext ('Bind g)

class SContextI (g :: Context) where
  witness :: SContext g

instance SContextI 'Null where
  witness = SNull

instance SContextI g => SContextI ('Bind g) where
  witness = SBind witness

-- Similarly `Var` is basically `Fin`.
data Var (g :: Context) where
  Z ::          Var ('Bind g)
  S :: Var g -> Var ('Bind g)

instance Eq (Var g) where
  Z   == Z   = True
  S m == S n = m == n
  _   == _   = False

instance Show (Var g) where
  show Z     = "Z"
  show (S n) = "S" ++ show n

----------------------------------------------------
-- ENVIRONMENTS
-- An Environment d e g associates, to each element of `g`, an element
-- of `e d`.
----------------------------------------------------

type Environment (d :: Context) e (g :: Context) = Var g -> e d

-- It can be constructed one element at a time by starting with the
-- empty environment and collecting one element in `e d` per element
-- in `g`.

null :: Environment d e 'Null
null v = case v of {}

cons :: Environment d e g -> e d -> Environment d e ('Bind g)
cons _   e Z     = e
cons env _ (S n) = env n

----------------------------------------------------
-- RENAMING
-- A well-known example of an environment
----------------------------------------------------

type Renaming g d = Environment d Var g

refl :: Renaming g g
refl = id

top :: Renaming g d -> Renaming g ('Bind d)
top = (S .)

pop :: Renaming g d -> Renaming ('Bind g) ('Bind d)
pop _   Z     = Z
pop ren (S n) = S $ ren n

trans :: Renaming g d -> Renaming d e -> Renaming g e
trans = flip (.)

{-
data Context a where
  None :: Context Void
  Bind :: Context a -> Context (Maybe a)

isEmpty :: Context a -> Bool
isEmpty None = True
isEmpty _    = False

class ValidContext a where
  witness :: Context a

instance ValidContext Void where
  witness = None

instance ValidContext a => ValidContext (Maybe a) where
  witness = Bind witness

diag :: forall f a. (ValidContext a, Functor f) =>
        (forall b. f (Maybe b)) -> (a -> f a)
diag emb = go witness
  where
    go :: forall b. Context b -> b -> f b
    go None     = absurd
    go (Bind c) = maybe emb $ fmap Just . go c

freshNames :: Context a -> [String] -> ([String], a -> String)
freshNames None     xs       = (xs, absurd)
freshNames (Bind c) (x : xs) = (ns, maybe x vars)
  where (ns, vars) = freshNames c xs
-}
