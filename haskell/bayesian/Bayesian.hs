{-# LANGUAGE TupleSections #-}

module Bayesian where

import Data.Ratio

newtype Bayesian a = Bayesian { unsafeRunBayesian :: [(Rational, a)] }


-- Here we group together the outcomes which are equal by summing their
-- probability. This is necessary because we may get the same outcome
-- from different runs.
runBayesian :: Eq a => Bayesian a -> [(Rational, a)]
runBayesian b = xs where

  (s, xs) = norm $ unsafeRunBayesian b
  norm    = foldr (\ (p, a) (s', ih) -> (p + s', insert (p / s) a ih)) (0, [])

  insert :: Eq a => Rational -> a -> [(Rational, a)] -> [(Rational, a)]
  insert p a [] = [(p, a)]
  insert p a (x@(q, b) : xs)
    | a == b    = (p + q , a) : xs
    | otherwise = x : insert p a xs


checkBayesian :: Eq a => a -> Bayesian a -> [(Rational, a)]
checkBayesian a  = filter ((a ==) . snd) . runBayesian

instance Functor Bayesian where
  fmap f = Bayesian . fmap (f <$>) . unsafeRunBayesian

instance Applicative Bayesian where
  pure      = Bayesian . pure . (1 % 1,)
  fs <*> ts = Bayesian [ (p * q, f t) | (p, f) <- unsafeRunBayesian fs
                                      , (q, t) <- unsafeRunBayesian ts ]

instance Monad Bayesian where
  return   = pure
  ts >>= f = Bayesian $ concatMap continuation $ unsafeRunBayesian ts where
    continuation (p, t) = fmap (\ (q, ft) -> (p * q, ft)) $ unsafeRunBayesian $ f t

bernouilli :: Rational -> Bayesian Bool
bernouilli p = Bayesian [ (p, True), (1-p, False) ]

observe :: Bool -> Bayesian Bool
observe b = if b then pure True else Bayesian []

epidemiology :: Bayesian Bool
epidemiology = do
  hasDisease     <- bernouilli (1 % 100)
  positiveResult <- if hasDisease
                    then bernouilli (80 % 100)
                    else bernouilli (96 % 1000)
  observe positiveResult
  return hasDisease


noTwoTails :: Bayesian (Bool, Bool)
noTwoTails = do
  heads1 <- bernouilli (1 % 2)
  heads2 <- bernouilli (1 % 2)
  observe (heads1 || heads2)
  return (heads1, heads2)

alarmRinging :: Bayesian Bool
alarmRinging = do
  burglar    <- bernouilli (1 % 1000)
  earthquake <- bernouilli (1 % 500)
  alarm      <- rings burglar earthquake
  observe =<< johnCalls alarm
  return burglar

  where

    johnCalls alarm = bernouilli $ if alarm then 9 % 10 else 1 % 20
    maryCalls alarm = bernouilli $ if alarm then 7 % 10 else 1 % 100

    rings b e = bernouilli $ case (b , e) of
      (True , True)  -> 95 % 100
      (True , False) -> 94 % 100
      (False, True)  -> 29 % 100
      (False, False) -> 1 % 1000
