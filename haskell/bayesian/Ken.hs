module Ken where

import Bayesian
import Data.Ratio

sample :: Integer -> Bayesian Rational
sample n = do
  lane  <- uniform [1..n]
  let p = lane % n
  rs <- mapM (const $ bernouilli p) [1..8]
  observe (length (filter id rs) == 5)
  pure p

winInLessThan :: Rational -> Integer -> Bayesian Bool
winInLessThan p 0 = pure False
winInLessThan p n = do
  v <- bernouilli p
  if v then pure True else winInLessThan p (n-1)

estimate :: Integer -> Bayesian Bool
estimate n = do
  p <- sample n
  winInLessThan p 3
