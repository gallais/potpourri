module Data.Array.ReadOnly

import Data.Buffer
import Data.DPair
import Data.Int.Order

%default total

------------------------------------------------------------------------
-- Arrays

||| Read-only array of elements of type `a`
||| @size is the size of the Buffer. It should be safe to access any element
|||       between 0 and `size`
||| @buffer contains the actual array
||| We do not export the constructor so that users may not unsafely manufacture arrays.
export
record Array (a : Type) where
  constructor MkArray
  size   : Subset Int (LTE 0)
  buffer : Buffer

||| A sub-array is delimited by two bounds
||| @begin for the beginning (0 for the full array)
||| @end   for the end       (size arr for the full array)
||| It is non empty if and only if `LT begin end`
public export
record SubArray {a : Type} (arr : Array a) where
  constructor MkSubArray
  begin : Subset Int (ClosedInterval 0 (fst (size arr)))
  end   : Subset Int (ClosedInterval 0 (fst (size arr)))

public export
boundaries : SubArray arr -> (Int, Int)
boundaries sub = (fst (begin sub), fst (end sub))

public export
middle : SubArray arr -> Int
middle = uncurry middle . boundaries

public export
whole : (arr : Array a) -> SubArray arr
whole arr =
  let 0 p : LTE 0 (fst (size arr)); p = snd (size arr)
  in MkSubArray (Element 0 (lbInClosedInterval p)) (Element _ (ubInClosedInterval p))

------------------------------------------------------------------------
-- Array ranges

namespace Array

  ||| We do not export the type publically so that the goals are more readable
  public export
  InRange : Array a -> (Int -> Type)
  InRange arr = Interval True False 0 (fst (size arr))

namespace SubArray

  ||| We do not export the type publically so that the goals are more readable
  public export
  InRange : SubArray arr -> (Int -> Type)
  InRange sub = Interval True False (fst (begin sub)) (fst (end sub))

||| Theorem: sub range inclusion
||| If a value is in range for a subarray then it is in range for the full array
export
0 inSubRange : {sub : SubArray arr} -> InRange sub i -> InRange arr i
inSubRange
  {sub = MkSubArray (Element b (MkInterval prfb _))
                    (Element e (MkInterval _ prfe))
  } (MkInterval isLB isUB)
  = MkInterval (trans prfb isLB) (trans_LT_LTE isUB prfe)

export
middleInRange : {sub : SubArray arr} ->
                uncurry LT (boundaries sub) -> InRange sub (middle sub)
middleInRange = middleInInterval

public export
cut : {i : Int} -> (sub : SubArray arr) -> (0 _ : InRange sub i) -> (SubArray arr, SubArray arr)
cut sub inR
  = let 0 inR' : InRange arr i; inR' = inSubRange inR in
    ( MkSubArray (begin sub) (Element i (inClosedInterval inR'))
    , MkSubArray (Element (i + 1) (inClosedInterval (sucInterval inR'))) (end sub)
    )

------------------------------------------------------------------------
-- Array value at position

||| Predicate specifying what the value in a given read-only array is at a
||| given index. The constructor for this predicate is proof-free because
||| the array is effectively external. It is not exported so that users may
||| craft their own, invalid, proofs.
export
data ValueAt : (arr : Array a) -> (i : Int) -> a -> Type where
  MkValueAt : ValueAt arr i v

||| Magic function stating that the predicate guarantees values are unique.
export
uniqueValueAt : ValueAt {a} arr i v -> ValueAt arr i w -> v === w
uniqueValueAt = believe_me (the (v === v) Refl)

||| The only mode of interaction with a read-only array: you may read it if
||| you are using an index.
export
interface Storable a where

  unsafeGetValueAt : HasIO io => (arr : Array a) -> (i : Int) -> io a

namespace Array

  ||| The blessed mode of interaction with a read-only array: not only do you
  ||| read the value but you get your hands on a proof that it is indeed the
  ||| value at the index you requested.
  export
  readValue : (HasIO io, Storable a) => (arr : Array a) ->
              (i : Int) -> (0 prf : InRange arr i) ->
              io (Subset a (ValueAt arr i))
  readValue arr i p = map (\ v => Element v MkValueAt) $ unsafeGetValueAt arr i

namespace SubArray

  ||| The blessed mode of interaction with a read-only subarray: not only do you
  ||| read the value but you get your hands on a proof that it is indeed the
  ||| value at the index you requested.
  export
  readValue : (HasIO io, Storable a) => {arr : Array a} -> (sub : SubArray arr) ->
              (i : Int) -> (0 prf : InRange sub i) ->
              io (Subset a (ValueAt arr i))
  readValue sub i p = readValue arr i (inSubRange p)
