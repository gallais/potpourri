module Data.Finite where

import Data.Bijection
import Data.DecidableSubset (DecidableSubset(..))

import Data.Maybe
import Data.List
import Data.Function

-- The assumption here is that \ g -> allValues !! index g == id
data Finite a = Finite
  { size      :: Integer
  , allValues :: [a]
  , index     :: a -> Integer
  }

range :: (Num a, Ord a, Enum a, Integral a) => a -> a -> Finite a
range lowerBound upperBound = Finite
  { size      = fromIntegral $ upperBound - lowerBound
  , allValues = [lowerBound..upperBound]
  , index     = \ a -> fromIntegral $ a - lowerBound
  }

cartesian :: Finite a -> Finite b -> Finite (a, b)
cartesian finA finB = Finite
  { size      = size finA * size finB
  , allValues = (,) <$> allValues finA <*> allValues finB
  , index     = \ (a, b) -> index finA a + size finB * index finB b
  }

union :: Eq a => Finite a -> Finite a -> Finite a
union finA finA' =
  let cleanedUp = nub $ ((++) `on` allValues) finA finA' in
  Finite
  { size      = genericLength cleanedUp
  , allValues = cleanedUp
  , index     = fromIntegral . fromJust . (`elemIndex` cleanedUp)
  }
  
intersection :: Eq a => DecidableSubset a a -> Finite a -> Finite a
intersection dec fin =
  let cleanedUp = catMaybes $ fmap (decide dec) $ allValues fin in
  Finite
  { size      = genericLength cleanedUp
  , allValues = cleanedUp
  , index     = fromIntegral . fromJust . (`elemIndex` cleanedUp)
  }

bijection :: Finite a -> Bijection a a' -> Finite a'
bijection fin bij = Finite
  { size      = size fin
  , allValues = fmap (forth bij) $ allValues fin
  , index     = index fin . back bij
  }
