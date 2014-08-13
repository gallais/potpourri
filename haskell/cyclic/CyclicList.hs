{-# LANGUAGE GADTs, RankNTypes, FlexibleInstances,
    ScopedTypeVariables, KindSignatures, ImpredicativeTypes #-}

module CyclicList where

import Prelude hiding (cycle, zipWith, all, and, or)
import Data.Void
import Data.Maybe
import Control.Monad
import qualified Prelude as Prelude
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
cfoldFinite c n xs | isFinite xs = Just $ cfold' c n xs
cfoldFinite c n xs | otherwise   = Nothing

reverse :: List a -> Maybe (List a)
reverse = cfoldFinite Cons CNil

sum :: Num a => List a -> Maybe a
sum = cfoldFinite (+) 0

product :: Num a => List a -> Maybe a
product = cfoldFinite (*) 1

maximum :: Ord a => List a -> a
maximum = List.maximum . getSupport

minimum :: Ord a => List a -> a
minimum = List.minimum . getSupport

repeat :: a -> List a
repeat x = CRec x id

replicate :: Int -> a -> List a
replicate n x = foldr (const $ Cons x) CNil [1..n]

fromCRec :: List a -> (a, forall b. CList a b -> CList a b)
fromCRec (CRec x r) = (x, r)

getCycle :: List a -> (a, [a])
getCycle (Cons x xs)   = getCycle xs
getCycle xs@(CRec x r) = (x, tail $ getSupport xs)

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
          m        = 1+ Prelude.length xtl
          n        = 1+ Prelude.length ytl
          lcmmn    = lcm m n
          xxtls    = join $ List.replicate (lcmmn `div` m) $ x : xtl
          yytls    = join $ List.replicate (lcmmn `div` n) $ y : ytl
      in cycle (f x y) $ tail $ List.zipWith f xxtls yytls

zip :: List a -> List b -> List (a, b)
zip = zipWith (,)

unzipLeft :: List (a, b) -> List a
unzipLeft = cmap fst

unzipRight :: List (a, b) -> List b
unzipRight = cmap snd

unzip :: List (a, b) -> (List a, List b)
unzip xs = (unzipLeft xs, unzipRight xs)

chead :: List a -> a
chead (Cons x _) = x
chead (CRec x _) = x

ctail :: List a -> List a
ctail CNil          = CNil
ctail (Cons _ xs)   = xs
ctail xs@(CRec x r) = r xs

null :: List a -> Bool
null CNil = True
null _    = False

length :: List a -> Maybe Int
length = cfoldRec (const $ fmap (1+)) (Just 0) (const $ const Nothing)

isFinite :: List a -> Bool
isFinite = isJust . CyclicList.length

isCyclic :: List a -> Bool
isCyclic = isNothing . CyclicList.length

intersperse :: forall a. a -> List a -> List a
intersperse x = cfold cons CNil crec
  where
    cons :: a -> forall ph. CList a ph -> CList a ph
    cons = \ y ys -> Cons y $ Cons x ys
    crec :: a -> (forall ph. CList a ph -> CList a ph) -> List a
    crec = \ y ih -> CRec y $ \ v -> Cons x $ ih v

take :: Int -> List a -> List a
take n = fromList . List.take n . toStream

instance Show a => Show (List a) where
  show = cfoldRec (\ x -> (++) (show x ++ " : ")) "[]"
                  (\ x ih -> "rec X. " ++ show x ++ " : " ++ ih "X")

instance Eq a => Eq (List a) where
  xs == ys = and $ zipWith (==) xs ys

toStream :: List a -> [ a ]
toStream = cfold' (:) []

fromList :: [a] -> List a
fromList = foldr Cons CNil
