module Data.Subset where

import Data.Bijection

newtype Subset s t = Subset { embed :: s -> t }

cartesian :: Subset a b -> Subset s t -> Subset (a, s) (b, t)
cartesian sAB sST = Subset { embed = \ (a, s) -> (embed sAB a, embed sST s) }

complement :: Subset a b -> Subset b b
complement _ = Subset id

bijection :: Subset a b -> Bijection a a' -> Bijection b b' -> Subset a' b'
bijection sAB bijAA' bijBB' = Subset $ forth bijBB' . embed sAB . back bijAA'
