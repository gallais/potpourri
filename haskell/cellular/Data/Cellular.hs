module Data.Cellular where

import Data.Subset
import Data.DecidableSubset
import Data.Finite

import Data.Maybe
import Data.Monoid
import Data.List
import Data.Function.Memoize
import Control.Monad.Identity

newtype CellularT m g a = Cellular { delta :: (g -> a) -> m a }

-- This type is quite annoying: we would like to have m (g -> a)
-- but, at the same time, still be able to have local side effects.

step :: Monoid g => CellularT m g a -> (g -> a) -> (g -> m a)
step (Cellular d) init g = d (init . (g <>))

-- Obviously, when we have a finite `g`, we're in luck:
stepA :: (Monoid g, Applicative m) =>
         Finite g -> CellularT m g a -> (g -> a) -> m (g -> a)
stepA fin cell init = fromTabulation <$> sequenceA tabulation
  where tabulation           = fmap (step cell init) $ allValues fin
        fromTabulation table = genericIndex table . index fin

runM :: (Eq g, Monoid g, Memoizable g,Monad m) =>
        Finite g -> CellularT m g a -> (g -> a) -> [m (g -> a)]
runM fin cell = iterate (fmap memoize . stepA fin cell =<<) . return

-- If we are only interested in a finite amount of steps then we can
-- run all the effects:
runFiniteM :: (Eq g, Monoid g, Memoizable g, Monad m) =>
              Integer -> Finite g -> CellularT m g a -> (g -> a) -> m [g -> a]
runFiniteM n fin = ((sequence . genericTake n) .) . runM fin


-- Obviously, we can have pure Cellular. And they are Actually a lot
-- easier to run:
type Cellular g a = CellularT Identity g a

run :: (Monoid g, Memoizable g) => Cellular g a -> (g -> a) -> [g -> a]
run cell = iterate $ (memoize .) $ (runIdentity .) . step cell


-- A PreCellular is a Cellular automata whose behaviour we only
-- observe on a subset of the whole Monoid

data PreCellularT m s g a =
  PreCellular { decidableSubset :: DecidableSubset s g
              , cellular        :: CellularT m g a }


stepPA :: (Monoid g, Applicative m) =>
          Finite s -> PreCellularT m s g a -> (g -> a) -> (s -> a) -> m (s -> a)
stepPA fin (PreCellular dec cell) dflt initS =
  fromTabulation <$> sequenceA tabulation
  where initG g              = maybe (dflt g) initS $ decide dec g
        range                = fmap (embed $ subset dec) $ allValues fin
        tabulation           = fmap (step cell initG) range
        fromTabulation table = genericIndex table . index fin

runPM :: (Monoid g, Memoizable s, Monad m) =>
         Finite s -> PreCellularT m s g a -> (Either s g -> a) -> [m (s -> a)]
runPM fin cell init = iterate (fmap memoize . stepPA fin cell (init . Right) =<<)
                    $ return (init . Left)

runFinitePM :: (Monoid g, Memoizable s, Monad m) =>
               Int -> Finite s -> PreCellularT m s g a -> (Either s g -> a) -> m [s -> a]
runFinitePM n fin cell = sequence . take n . runPM fin cell

