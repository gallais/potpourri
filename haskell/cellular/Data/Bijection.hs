module Data.Bijection where

import Data.Monoid

data Bijection a b = Bijection
  { forth :: a -> b
  , back  :: b -> a
  }

inverse :: Bijection a b -> Bijection b a
inverse bij = Bijection
  { forth = back bij
  , back  = forth bij
  }

pair :: Bijection a b -> Bijection c d -> Bijection (a, c) (b, d)
pair bijAB bijCD = Bijection
  { forth = \ (a, c) -> (forth bijAB a, forth bijCD c)
  , back  = \ (b, d) -> (back bijAB b, back bijCD d)
  }

identity :: Bijection a a
identity = Bijection id id

monoidSum :: Bijection a (Sum a)
monoidSum = Bijection
  { forth = Sum
  , back  = getSum
  }
