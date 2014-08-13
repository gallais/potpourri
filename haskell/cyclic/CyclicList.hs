{-# LANGUAGE GADTs, RankNTypes, FlexibleInstances,
    ScopedTypeVariables, KindSignatures #-}

module CyclicList where

import Prelude hiding (cycle, zipWith)
import Data.Void
import Control.Monad
import qualified Data.List as List

data Closed = Closed
type List a = CList a Closed

data CList a b where
  CNil :: CList a Closed
  Cons :: a -> CList a b -> CList a b
  CRec :: a -> (forall b. CList a b -> CList a b) -> CList a Closed

cfold :: forall a (b :: * -> *).
         (forall ph. a -> b ph -> b ph) ->
         b Closed ->
         (a -> (forall ph. b ph -> b ph) -> b Closed) ->
         List a ->
         b Closed
cfold c n r = goCRec
  where
    goCRec :: forall ph. CList a ph -> b ph
    goCRec CNil          = n
    goCRec (Cons x xs)   = c x $ goCRec xs
    goCRec xs@(CRec x p) = r x $ stopCRec (p xs)

    stopCRec :: CList a Closed -> forall ph. b ph -> b ph
    stopCRec (Cons x xs) ih = c x $ stopCRec xs ih
    stopCRec (CRec _ _)  ih = ih

cmap :: forall a b. (a -> b) -> List a -> List b
cmap f = cfold (Cons . f) CNil (CRec . f)

newtype Lift a b = Lift { out :: a }

cfoldRec :: forall a b. (a -> b -> b) -> b ->
            (a -> (b -> b) -> b) -> List a -> b
cfoldRec c n r xs = out $ cfold c' (Lift n) r' xs
  where
    c' :: forall ph. a -> Lift b ph -> Lift b ph
    c' a    = Lift . c a . out
    r' :: a -> (forall ph. Lift b ph -> Lift b ph) -> Lift b Closed
    r' a ih = Lift $ r a (out . ih . Lift)

cfold' :: forall a b. (a -> b -> b) -> b -> List a -> b
cfold' c n = cfoldRec c n r
  where
    r :: a -> (b -> b) -> b
    r a ih = c a (ih $ r a ih)

append :: List a -> List a -> List a
append xs ys = cfold Cons ys CRec xs

singleton :: a -> List a
singleton x = Cons x CNil

cycle :: a -> [a] -> List a
cycle x xs = CRec x $ \ v -> foldr Cons v xs

getCycle :: List a -> (a, [a])
getCycle (Cons x xs)   = getCycle xs
getCycle xs@(CRec x r) = (x, getSupport $ r xs)
  where
    getSupport (Cons x xs) = x : getSupport xs
    getSupport (CRec _ _)  = []

unfoldOne :: a -> (forall b. CList a b -> CList a b) -> List a
unfoldOne x r =
  case getCycle (CRec x r) of
    (y, [])     -> Cons y $ CRec y id
    (y, z : zs) -> Cons y $ cycle z $ zs ++ [y]

zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith f = go
  where
    go CNil          _             = CNil
    go _             CNil          = CNil
    go (Cons x xs)   (Cons y ys)   = Cons (f x y) $ go xs ys
    go xs@(Cons _ _) (CRec y ry)   = go xs (unfoldOne y ry)
    go (CRec x rx)   ys@(Cons _ _) = go (unfoldOne x rx) ys
    go xs@(CRec _ _) ys@(CRec _ _) =
      let (x, xtl) = getCycle xs
          (y, ytl) = getCycle ys
          m        = 1+ length xtl
          n        = 1+ length ytl
          lcmmn    = lcm m n
          xxtls    = join $ List.replicate (lcmmn `div` m) $ x : xtl
          yytls    = join $ List.replicate (lcmmn `div` n) $ y : ytl
      in cycle (f x y) $ tail $ List.zipWith f xxtls yytls

ctail :: List a -> List a
ctail CNil          = CNil
ctail (Cons _ xs)   = xs
ctail xs@(CRec x r) = r xs

clist1 :: List Int
clist1 = CRec 1 $ \ xs -> Cons 2 xs

-- clist1' :: List Int
-- clist1' = CRec $ \ xs -> CRec $ \ ys -> Cons 1 $ Cons 2 xs
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
clist3 :: List Int
clist3 = CRec 1 (Cons 2 . Cons 3)

-- acyclic :: List Int
-- acyclic = CRec $ \ xs -> Cons 1 $ cmap (+1) xs
-------------------------------------------------------------
-- Rigtfully rejected: this is not a cyclic definition!
-------------------------------------------------------------
{-
    Couldn't match type `(forall b.
                          CList (List Integer -> CList Integer Closed) b
                          -> CList (List Integer -> CList Integer Closed) b)
                         -> CList (List Integer -> CList Integer Closed) Closed'
                  with `CList Int Closed'
    Expected type: List Int
      Actual type: (forall b.
                    CList (List Integer -> CList Integer Closed) b
                    -> CList (List Integer -> CList Integer Closed) b)
                   -> CList (List Integer -> CList Integer Closed) Closed
    In the expression: CRec $ \ xs -> Cons 1 $ cmap (+ 1) xs
    In an equation for `acyclic':
        acyclic = CRec $ \ xs -> Cons 1 $ cmap (+ 1) xs
-}

instance Show a => Show (List a) where
  show = cfoldRec (\ x -> (++) (show x ++ " : ")) "[]"
                  (\ x ih -> "rec X. " ++ show x ++ " : " ++ ih "X")

toStream :: List a -> [ a ]
toStream = cfold' (:) []
