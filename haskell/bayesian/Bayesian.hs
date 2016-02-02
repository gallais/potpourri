{-# LANGUAGE TupleSections #-}

module Bayesian where

import Data.Ratio

newtype Bayesian a = Bayesian { unsafeRunBayesian :: [(Rational, a)] }

runBayesian :: Bayesian a -> [(Rational, a)]
runBayesian b = xs where
  -- yay circular programs!
  (s, xs) = norm $ unsafeRunBayesian b
  norm    = foldr (\ (p, a) (s', ih) -> (p + s', (p / s, a) : ih)) (0, [])

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
