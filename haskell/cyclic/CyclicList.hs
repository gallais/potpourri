{-# LANGUAGE GADTs, RankNTypes, FlexibleInstances, ScopedTypeVariables #-}

module CyclicList where

import Data.Void

data Finite = Finite
data Bound  = Bound
data Closed = Closed
type List a = CList a Closed

data CList a b where
  CNil :: CList a b
  Cons :: a -> CList a b -> CList a b
  CRec :: a -> (forall b. CList a b -> CList a b) -> CList a Closed

-- unfortunately, cmap unfolds the list (cf. CRec case)
-- because the contravariance in CRec makes it impossible
-- to build another CRec.
cmap :: forall a b. (a -> b) -> List a -> List b
cmap f xs = goCRec xs
  where
    goCRec :: forall ph. CList a ph -> CList b ph
    goCRec CNil          = CNil
    goCRec (Cons x xs)   = Cons (f x) $ goCRec xs
    goCRec xs@(CRec x r) = CRec (f x) $ \ bs -> stopCRec bs (r xs)

    stopCRec :: forall ph. CList b ph -> CList a Closed -> CList b ph
    stopCRec bs CNil        = CNil
    stopCRec bs (Cons x xs) = Cons (f x) $ stopCRec bs xs
    stopCRec bs (CRec _ _)  = bs

data Subst a b c where
  Empty :: Subst a b b
  AnElt :: a -> Subst a () Void

ctail :: List a -> List a
ctail CNil          = CNil
ctail (Cons _ xs)   = xs
ctail xs@(CRec x r) = r xs


clist1 :: List Int
clist1 = CRec 1 $ \ xs -> Cons 2 xs

-- clist1' :: List Int
-- clist1' = CRec $ \ xs -> CRec $ \ ys -> Cons 1 $ Cons 2 ys
-------------------------------------------------------------
-- Rightfully rejected: we want a canonical representation!
-------------------------------------------------------------
{-    Couldn't match type `b' with `Closed'
      `b' is a rigid type variable bound by
          a type expected by the context: CList Int b -> CList Int b
          at Cyclic.hs:22:11
    Expected type: CList Int b
      Actual type: CList Int Closed
    In the expression: CRec $ \ ys -> Cons 1 $ Cons 2 ys
    In the second argument of `($)', namely
      `\ xs -> CRec $ \ ys -> Cons 1 $ Cons 2 ys'
-}

clist2 :: List Int
clist2 = Cons 1 $ CRec 2 $ \ xs -> Cons 3 xs

-- acyclic :: List Int
-- acyclic = CRec $ \ xs -> Cons 1 $ cmap (+1) xs
-------------------------------------------------------------
-- Rigtfully rejected: this is not a cyclic definition!
-------------------------------------------------------------
{-    Couldn't match type `b' with `Closed'
      `b' is a rigid type variable bound by
          a type expected by the context: CList Int b -> CList Int b
          at Cyclic.hs:28:11
    Expected type: List Int
      Actual type: CList Int b
    In the second argument of `cmap', namely `xs'
    In the second argument of `($)', namely `cmap (+ 1) xs'
-}

data Stop = Stop

stop :: CList a Stop
stop = CNil

instance Show a => Show (CList a Stop) where
  show (Cons x xs) = show x ++ " : " ++  show xs
  show CNil = "X"

instance Show a => Show (List a) where
  show CNil        = "[]"
  show (Cons x xs) = show x ++ " : " ++  show xs
  show (CRec x r)  = "fix X. " ++ show (Cons x $ r stop)

toStream :: List a -> [ a ]
toStream CNil          = []
toStream (Cons x xs)   = x : toStream xs
toStream xs@(CRec x r) = x : toStream (r xs)

