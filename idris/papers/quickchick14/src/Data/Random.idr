module Data.Random

import Codata.BTree
import Data.DPair
import Data.Nat
import Data.So
import Data.Vect

%default total

export
data Seed : Type where [external]

export
new : Seed

export
split : Seed -> (Seed, Seed)

export
splits : Seed -> (n : Nat) -> Vect n Seed
splits s Z = []
splits s (S n) =
  let (s1, s2) = split s in
  s1 :: splits s2 n

export
splitSurjective : (s1, s2 : Seed) -> Exists $ \ s => split s === (s1, s2)

export
mkBTree : Seed -> BTree Seed
mkBTree = unfold $ \ s => let (sl, sr) = split s in (s, sl, sr)

export
varySeed : Path -> Seed -> Seed
varySeed p s = index p (mkBTree s)

public export
record Interval (a : Type) {auto o : Ord a} where
  constructor MkInterval
  lowerBound  : a
  upperBound  : a
  validBounds : So (lowerBound <= upperBound)

public export
record In (a : Type) {auto o : Ord a} (bnds : Interval a @{o}) where
  constructor MkIn
  value        : a
  isLowerBound : So (bnds.lowerBound <= value)
  isUpperBound : So (value <= bnds.upperBound)

randomRBool : Interval Bool -> Seed -> (Bool, Seed)

randomRNat : Interval Nat -> Seed -> (Nat, Seed)

public export
interface Random a where
  random : Seed -> (a, Seed)

export
{bnds : ?} -> Random (In Bool bnds) where
  random s = mapFst coerce (randomRBool bnds s) where
    coerce : Bool -> In Bool bnds
    coerce b = MkIn b (believe_me Oh) (believe_me Oh)

export
{bnds : ?} -> Random (In Nat bnds) where
  random s = mapFst coerce (randomRNat bnds s) where
    coerce : Nat -> In Nat bnds
    coerce b = MkIn b (believe_me Oh) (believe_me Oh)

export
zeroMin : {m : Nat} -> So (Z <= m)
zeroMin {m = Z}   = Oh
zeroMin {m = S m} = Oh

export
{n : Nat} -> {0 prf : So (Z <= n)} ->
  Cast (In Nat (MkInterval 0 n prf)) (Fin (S n)) where
  cast (MkIn 0     isLB isUB) = FZ
  cast (MkIn (S k) isLB isUB) = FS $ case n of
    0   => absurd isUB
    S m => cast {from = In Nat (MkInterval Z m zeroMin)} (MkIn k zeroMin isUB)

export
{n : Nat} -> Random (Fin (S n)) where
  random s = mapFst cast $ random {a = In Nat $ MkInterval 0 n zeroMin} s
