{-# LANGUAGE FlexibleContexts #-}

module Data.Cellular where

import Data.Subset
import Data.DecidableSubset

import Data.Maybe
import Data.Monoid
import Data.List
import Data.Function.MemoM
import Control.Monad.Identity

newtype CellularT m g a = Cellular { delta :: (g -> m a) -> m a }

-- This type is quite annoying: we would like to have m (g -> a)
-- but, at the same time, still be able to have local side effects.

stepM :: (Monoid g, Monad m) => CellularT m g a -> (g -> m a) -> (g -> m a)
stepM cell init g = delta cell $ init . (g <>)


runM :: (Monoid g, Ord g, Monad m) => CellularT m g a -> (g -> m a) -> [g -> m a]
runM cell = iterate (memoM . stepM cell)

-- Obviously, we can have pure Cellular. And they are Actually a lot
-- easier to run:
type Cellular g a = CellularT Identity g a

-- run :: (Monoid g, Ord g, MonadMemo g a Identity) => Cellular g a -> (g -> a) -> [g -> a]
run cell = fmap (runIdentity .) . runM cell . (Identity .)

-- A PreCellular is a Cellular automata whose behaviour we only
-- observe on a subset of the whole Monoid

data PreCellularT m s g a =
  PreCellular { decidableSubset :: DecidableSubset s g
              , cellular        :: CellularT m g a }

stepPM :: (Monoid g, Monad m) =>
          PreCellularT m s g a -> (g -> m a) -> (s -> m a) -> (s -> m a)
stepPM (PreCellular dec cell) dflt initS = stepM cell initG . embed (subset dec)
  where initG g = maybe (dflt g) initS $ decide dec g

runPM :: (Monoid g, Ord s, Monad m) =>
         PreCellularT m s g a -> (Either s g -> m a) -> [s -> m a]
runPM cell init = iterate (memoM . stepPM cell (init . Right)) (init . Left)
