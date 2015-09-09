module Data.DecidableSubset where

import Data.Bijection
import Data.Subset (Subset(..))
import qualified Data.Subset as Subset

import Data.Maybe
import Data.List
import Control.Monad

data DecidableSubset s t = DecidableSubset
  { subset :: Subset s t
  , decide :: t -> Maybe s
  }

range :: Ord a => a -> a -> DecidableSubset a a
range lowerBound upperBound = DecidableSubset
  { subset = Subset id
  , decide = \ n -> guard (lowerBound <= n && n <= upperBound) >> return n
  }

complement :: DecidableSubset s t -> DecidableSubset t t
complement dec = DecidableSubset
  { subset = Subset.complement (subset dec)
  , decide = \ t -> maybe (Just t) (const Nothing) $ decide dec t
  }

cartesian :: DecidableSubset a b -> DecidableSubset s t -> DecidableSubset (a, s) (b, t)
cartesian decAB decST = DecidableSubset
  { subset = Subset.cartesian (subset decAB) (subset decST)
  , decide = \ (a, s) -> (,) <$> decide decAB a <*> decide decST s
  }

intersection :: DecidableSubset a b -> DecidableSubset a b -> DecidableSubset a b
intersection decAB decAB' = DecidableSubset
  { subset = subset decAB
  , decide = \ t -> decide decAB t >> decide decAB' t
  } 

bijection :: DecidableSubset a b -> Bijection a a' -> Bijection b b' -> DecidableSubset a' b'
bijection decAB bijAA' bijBB' = DecidableSubset
  { subset = Subset.bijection (subset decAB) bijAA' bijBB'
  , decide = fmap (forth  bijAA') . decide decAB . back bijBB'
  }
