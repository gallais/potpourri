module Plot where

import Graphics.Gnuplot.Simple

data Nat = O | Suc Nat

toInt :: Nat -> Int
toInt O       = 0
toInt (Suc n) = 1 + toInt n

plot :: String -> [Nat] -> [Nat] -> IO ()
plot file xs ys = epspdfPlot file (\ attr -> plotPath attr $ zipWith (\ x y -> (toInt x, toInt y)) xs ys)
