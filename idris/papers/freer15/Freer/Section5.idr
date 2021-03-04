module Freer.Section5

import Relation.Binary.Closure.Transitive
import Data.List.AtIndex
import Data.OpenUnion
import Freer.Section3p1
import Freer.Section3p2

%default total

public export
data Ndet : Type -> Type where
  MZero : Ndet a
  MPlus : Ndet Bool

public export
Member Ndet ts => Alternative (Eff ts) where
  empty = send MZero
  l <|> r = send MPlus >>= \ b => if b then l else r

infixr 5 <|!>
(<|!>) : Alternative f => f a -> f a -> f a
f <|!> g = f <|> g

public export
makeChoiceA : Alternative f => Eff (Ndet :: ts) a -> Eff ts (f a)
makeChoiceA = handleOrRelay (pure . pure) $ \ m, k => case m of
  MZero => pure empty
  MPlus => [| k True <|!> k False |]

public export
msum : Alternative f => List (f a) -> f a
msum = foldr (<|!>) empty

public export
covering
msplit : Member Ndet ts => Eff ts a -> Eff ts (Maybe (a, Eff ts a))
msplit = loop [] where

  loop : List (Eff ts a) -> Eff ts a -> Eff ts (Maybe (a, Eff ts a))
  loop alts (Pure a) = pure (Just (a, msum alts))
  loop alts (Impure x k) = case prj {t = Ndet} x of
    Just MZero => case alts of
      [] => pure Nothing
      (c::alts) => loop alts c
    Just MPlus => loop ((qApp k False) :: alts) (qApp k True)
    _ => Impure x (^ \ v => loop alts (qApp k v))

public export
covering
ifte : Member Ndet ts => Eff ts a -> (a -> Eff ts b) -> Eff ts b -> Eff ts b
ifte b l r = msplit b >>= \case
  Nothing => r
  Just (a, mas) => l a <|> (mas >>= l)
