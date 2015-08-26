module Data.Cellular where

import Data.SubSet
import Data.Monoid
import Data.Function.Memoize

newtype Cellular g a = Cellular { delta :: (g -> a) -> a }

step :: Monoid g => Cellular g a -> (g -> a) -> (g -> a)
step (Cellular d) init g = d (init . (g <>))

run :: (Monoid g, Memoizable g) => Cellular g a -> (g -> a) -> [g -> a]
run = iterate . (memoize .) . step

data PreCellular s g a =
  PreCellular { decidableSubSet :: DecidableSubSet s g
              , cellular        :: Cellular g a }

stepP :: Monoid g => PreCellular s g a -> (g -> a) -> (s -> a) -> (s -> a)
stepP (PreCellular dec cell) dflt initS = step cell init . sToG
  where sToG   = embed (subSet dec)
        init g = maybe (dflt g) initS $ decide dec g

runP :: (Monoid g, Memoizable s) =>
        PreCellular s g a -> (Either s g -> a) -> [s -> a]
runP preCell init = iterate (memoize . stepP preCell (init . Right)) (init . Left)
