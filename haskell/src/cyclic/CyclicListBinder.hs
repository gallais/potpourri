{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, KindSignatures #-}

module CyclicListBinder where

import Data.Void

type List a = CList a Void

data CList a b where
  CNil :: CList a Void
  CVar :: CList a ()
  Cons :: a -> CList a b -> CList a b
  CRec :: a -> CList a () -> CList a Void

data Subst (a :: * -> *) b where
  Empty :: Subst a Void
  AnElt :: a Void -> Subst a ()

clist1 :: List Int
clist1 = CRec 1 $ Cons 2 CVar

clist2 :: List Int
clist2 = Cons 1 $ CRec 2 $ Cons 3 CVar

cfold :: forall a (b :: * -> *) c.
         (forall i. a -> b i -> b i) ->
         b Void ->
         (b Void -> b ()) ->
         (a -> b () -> b Void) -> List a -> b Void
cfold c n v r = go Empty
  where
    go :: Subst b i -> CList a i -> b i
    go Empty      CNil           = n
    go s          (Cons x xs)    = c x $ go s xs
    go (AnElt ih) CVar           = v ih
    go s          mu@(CRec x xs) = r x $ go (AnElt $ go s mu) xs

cmap :: forall a b c. (a -> b) -> List a -> List b
cmap f = cfold (Cons . f) CNil (\ _ -> CVar) (CRec . f)

newtype Lift a b = Lift { out :: a }

cfold' :: forall a b. (a -> b -> b) -> b -> List a -> b
cfold' c n = out . cfold c' (Lift n) v' r'
  where
    c' :: forall i. a -> Lift b i -> Lift b i
    c' a = Lift . c a . out
    v'   = Lift . out
    r' a = Lift . c a . out

-- clist3 :: List Int
-- clist3 = CRec 1 $ cmap (+1) CVar
-- Rightfully rejected
{-
    Couldn't match expected type `()' with actual type `Void'
    Expected type: CList a0 ()
      Actual type: List a0
    In the return type of a call of `cmap'
    In the second argument of `($)', namely `cmap (+ 1) CVar'
-}

fromList :: [a] -> List a
fromList = foldl (flip Cons) CNil

toStream :: forall a. List a -> [a]
toStream = cfold' (:) []

append :: List a -> List a -> List a
append xs ys = cfold Cons ys (\ _ -> CVar) CRec xs

instance Show a => Show (CList a b) where
  show CNil        = "[]"
  show (Cons x xs) = show x ++ " : " ++ show xs
  show CVar        = "X"
  show (CRec x xs) = "fix X. " ++ show x ++ " : " ++ show xs
