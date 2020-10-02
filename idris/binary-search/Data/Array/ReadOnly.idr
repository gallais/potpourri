module Data.Array.ReadOnly

import Data.Buffer
import Data.DPair
import Data.Int.Order

%default total

-- ||| Read-only array of elements of type `a`
export
record Array (a : Type) where
  constructor MkArray
  size   : Int
  buffer : Buffer

-- ||| Index in range of the array bounds
export
record InRange (lb, ub, i : Int) where
  constructor MkInRange
  lowerBound : LTE lb i
  upperBound : LT i ub

-- ||| Assuming that `lb < ub`, `lb <= middle < ub`
-- ||| No risk of overflow.
public export
middle : (lb, ub : Int) -> Int
middle lb ub = lb + ((ub - lb) `shiftR` 1)

export
middleInRange : {lb, ub : Int} -> LT lb ub -> InRange lb ub (middle lb ub)
middleInRange p = let (lb, ub) = Order.middle p in MkInRange lb ub

-- ||| Predicate specifying what the value in a given read-only array is at a
-- ||| given index. The constructor for this predicate is proof-free because
-- ||| the array is effectively external. It is not exported so that users may
-- ||| craft their own, invalid, proofs.
export
data ValueAt : (arr : Array a) -> (i : Int) -> a -> Type where
  MkValueAt : ValueAt arr i v

-- ||| Magic function stating that the predicate guarantees values are unique.
export
uniqueValueAt : ValueAt {a} arr i v -> ValueAt arr i w -> v === w
uniqueValueAt = believe_me (the (v === v) Refl)

-- ||| The only mode of interaction with a read-only array: you may read it if
-- ||| you are using an index.
export
interface Storable a where

  unsafeGetValueAt : HasIO io => (arr : Array a) -> (i : Int) -> io a

-- ||| The blessed mode of interaction with a read-only array: not only do you
-- ||| read the value but you get your hands on a proof that it is indeed the
-- ||| value at the index you requested.
export
readValue : (HasIO io, Storable a) => (arr : Array a) ->
            (i : Int) -> (0 prf : InRange 0 (size arr) i) ->
            io (Subset a (ValueAt arr i))
readValue arr i p = map (\ v => Element v MkValueAt) $ unsafeGetValueAt arr i
