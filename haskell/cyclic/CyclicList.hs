{-# LANGUAGE GADTs, RankNTypes, ImpredicativeTypes,
    ScopedTypeVariables, KindSignatures #-}

module CyclicList where

import Prelude hiding (cycle, zipWith, all, and, or, head, last, tail)
import Data.Void
import Data.Maybe
import Control.Monad
import qualified Prelude as Prelude
import qualified Data.List as List

data Closed = Closed
newtype List a = List { clist :: CList a Closed }

data CList a b where
  CNil :: CList a Closed
  Cons :: a -> CList a b -> CList a b
  CRec :: a -> (forall b. CList a b -> CList a b) -> CList a Closed

cnil :: List a
cnil = List CNil

cons :: a -> List a -> List a
cons a = List . Cons a . clist

cycle :: a -> [a] -> List a
cycle x xs = List $ CRec x $ \ v -> foldr Cons v xs

repeat :: a -> List a
repeat x = List $ CRec x id

cfold :: forall a (b :: * -> *).
         (forall ph. a -> b ph -> b ph) ->
         b Closed ->
         (a -> (forall ph. b ph -> b ph) -> b Closed) ->
         List a ->
         b Closed
cfold c n r = goCRec . clist
  where
    goCRec :: forall ph. CList a ph -> b ph
    goCRec CNil          = n
    goCRec (Cons x xs)   = c x $ goCRec xs
    goCRec xs@(CRec x p) = r x $ stopCRec (p xs)

    stopCRec :: CList a Closed -> forall ph. b ph -> b ph
    stopCRec (Cons x xs) ih = c x $ stopCRec xs ih
    stopCRec (CRec _ _)  ih = ih

cmap :: forall a b. (a -> b) -> List a -> List b
cmap f = List . cfold (Cons . f) CNil (CRec . f)

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
append xs ys = List $ cfold Cons (clist ys) CRec xs

singleton :: a -> List a
singleton x = cons x cnil

getSupport :: List a -> [a]
getSupport = cfoldRec (:) [] (\ a -> (:) a . ($ []))

and :: List Bool -> Bool
and = cfoldRec (&&) True (\ a -> (&&) a . ($ True))

or :: List Bool -> Bool
or = cfoldRec (||) False (\ a -> (||) a . ($ False))

all :: (a -> Bool) -> List a -> Bool
all p = and . cmap p

any :: (a -> Bool) -> List a -> Bool
any p = or . cmap p

cfoldFinite :: (a -> b -> b) -> b -> List a -> Maybe b
cfoldFinite c n = cfoldRec (\ a -> fmap (c a)) (Just n) crec
  where crec = const $ const Nothing

reverse :: List a -> Maybe (List a)
reverse = cfoldFinite cons cnil

sum :: Num a => List a -> Maybe a
sum = cfoldFinite (+) 0

product :: Num a => List a -> Maybe a
product = cfoldFinite (*) 1

maximumBy :: (a -> a -> Ordering) -> List a -> a
maximumBy ord = List.maximumBy ord . getSupport

minimumBy :: (a -> a -> Ordering) -> List a -> a
minimumBy ord = List.minimumBy ord . getSupport

maximum :: Ord a => List a -> a
maximum = List.maximum . getSupport

minimum :: Ord a => List a -> a
minimum = List.minimum . getSupport


replicate :: Int -> a -> List a
replicate n x = foldr (const $ cons x) cnil [1..n]

fromCRec :: List a -> (a, forall b. CList a b -> CList a b)
fromCRec (List (CRec x r)) = (x, r)

getCycle :: List a -> (a, [a])
getCycle = go . clist
  where go (Cons x xs)   = go xs
        go xs@(CRec x r) = (x, List.tail $ getSupport $ List xs)

unfoldOne :: a -> (forall b. CList a b -> CList a b) -> List a
unfoldOne x r =
  case getCycle (List $ CRec x r) of
    (y, [])     -> cons y $ List $ CRec y id
    (y, z : zs) -> cons y $ cycle z $ zs ++ [y]

zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith f xs ys = go (clist xs) (clist ys)
  where
    go CNil          _             = cnil
    go _             CNil          = cnil
    go (Cons x xs)   (Cons y ys)   = cons (f x y) $ go xs ys
    go xs@(Cons _ _) (CRec y ry)   = go xs (clist $ unfoldOne y ry)
    go (CRec x rx)   ys@(Cons _ _) = go (clist $ unfoldOne x rx) ys
    go xs@(CRec _ _) ys@(CRec _ _) =
      let (x, xtl) = getCycle $ List xs
          (y, ytl) = getCycle $ List ys
          m        = 1+ Prelude.length xtl
          n        = 1+ Prelude.length ytl
          lcmmn    = lcm m n
          xxtls    = join $ List.replicate (lcmmn `div` m) $ x : xtl
          yytls    = join $ List.replicate (lcmmn `div` n) $ y : ytl
      in cycle (f x y) $ List.tail $ List.zipWith f xxtls yytls

zip :: List a -> List b -> List (a, b)
zip = zipWith (,)

unzipLeft :: List (a, b) -> List a
unzipLeft = cmap fst

unzipRight :: List (a, b) -> List b
unzipRight = cmap snd

unzip :: List (a, b) -> (List a, List b)
unzip xs = (unzipLeft xs, unzipRight xs)

head :: List a -> Maybe a
head = cfoldRec (const . Just) Nothing (const . Just)

last :: List a -> Maybe a
last xs = head xs >>= flip go (clist xs)
  where
    go :: a -> CList a b -> Maybe a
    go x CNil        = Just x
    go _ (Cons x xs) = go x xs
    go _ (CRec _ _)  = Nothing

tail :: List a -> Maybe (List a)
tail = fmap List . go . clist
  where
   go CNil          = Nothing
   go (Cons _ xs)   = Just xs
   go xs@(CRec x r) = Just $ r xs

null :: List a -> Bool
null (List CNil) = True
null _           = False

length :: List a -> Maybe Int
length = cfoldFinite (const (1+)) 0

isFinite :: List a -> Bool
isFinite = isJust . CyclicList.length

isCyclic :: List a -> Bool
isCyclic = isNothing . CyclicList.length

intersperse :: forall a. a -> List a -> List a
intersperse x = List . cfold cons CNil crec
  where
    cons :: a -> forall ph. CList a ph -> CList a ph
    cons = \ y ys -> Cons y $ Cons x ys
    crec :: a -> (forall ph. CList a ph -> CList a ph) ->
            CList a Closed
    crec = \ y ih -> CRec y $ \ v -> Cons x $ ih v

take :: Int -> List a -> List a
take n = fromList . List.take n . toStream

instance Show a => Show (List a) where
  show = cfoldRec (\ x -> (++) (show x ++ " : ")) "[]"
                  (\ x ih -> "rec X. " ++ show x ++ " : " ++ ih "X")

instance Eq a => Eq (List a) where
  xs == ys = and $ zipWith (==) xs ys

instance Functor List where
  fmap = cmap

toStream :: List a -> [a]
toStream = cfold' (:) []

toList :: List a -> Maybe [a]
toList = cfoldFinite (:) []

fromList :: [a] -> List a
fromList = foldr cons cnil
