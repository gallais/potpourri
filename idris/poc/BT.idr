module BT

import Data.Buffer
import Data.Nat
import Data.DPair
import Decidable.Equality

%default total

public export
LT : Int -> Int -> Type
LT a b = compare a b === LT

public export
GT : Int -> Int -> Type
GT a b = compare a b === GT

public export
LE : Int -> Int -> Type
LE a b = Not (GT a b)

export
record Array (a : Type) where
  constructor MkArray
  size   : Int
  buffer : Buffer

export
data ValueAt : (arr : Array a) -> (i : Int) -> a -> Type where
  MkValueAt : ValueAt arr i v

export
uniqueValueAt : ValueAt {a} arr i v -> ValueAt arr i w -> v === w
uniqueValueAt = believe_me (the (v === v) Refl)

export
readValue : HasIO io => (arr : Array Bits64) -> (i : Int) ->
            IO (Subset Bits64 (ValueAt arr i))
readValue arr i = map (\ v => Element v MkValueAt) $ getBits64 arr.buffer i

data Extended a = MInf | PInf | Lift a

data ExtendedLT : (a -> a -> Type) -> (Extended a -> Extended a -> Type) where
  MInfPInf : ExtendedLT lt MInf PInf
  MInfLift : ExtendedLT lt MInf (Lift v)
  LiftLift : {0 v, w : a} -> lt v w -> ExtendedLT lt (Lift v) (Lift w)
  LiftPInf : ExtendedLT lt (Lift v) PInf

-- ||| The inductive type `BT lt arr lbI lbV ubI ubV` is a proof that between
-- ||| the indices `lbI` and `ubI` the array `arr` is sorted containing values
-- ||| bounded by `lbV` and `ubV`.
-- ||| The proof takes the form of a binary search tree which should allow us
-- ||| to efficiently explore the array in an obviously terminating way!

data BT : (lt : a -> a -> Type) ->                -- strict order
          (arr : Array a) ->                      -- array of data
          (lbI : Int) -> (lbV : Extended a) ->    -- lower index & value
          (ubI : Int) -> (ubV : Extended a) ->    -- upper index & value
          Type where
  Empty : GT lbI ubI -> BT lt arr lbI lbV ubI ubV
  Node  : {0 a : Type} -> {0 lt : a -> a -> Type} -> {0 arr : Array a} ->
          {0 lbI, ubI : Int} -> {0 lbV, ubV : Extended a} ->
          LE lbI ubI ->
          -- this is (lbI + ubI) `div` 2 but without risk of overflow
          let middle = lbI + (ubI - lbI) `div` 2 in
          {0 v : a} -> ValueAt arr middle v ->
          ExtendedLT lt lbV (Lift v) -> ExtendedLT lt (Lift v) ubV ->
          BT lt arr lbI lbV (middle - 1) (Lift v) ->
          BT lt arr (middle + 1) (Lift v) ubI ubV ->
          BT lt arr lbI lbV ubI ubV

Inside : (lt : a -> a -> Type) -> (arr : Array a) ->
         Int -> Extended a ->
         Int -> Extended a ->
         (Int, a) -> Type
Inside lt arr lbI lbV ubI ubV (i, v) =
  ( LE lbI i
  , LE i ubI
  , ValueAt arr i v
  , ExtendedLT lt lbV (Lift v)
  , ExtendedLT lt (Lift v) ubV
  )

-- TODO: implement
search : (arr : Array a) ->
         (lbI, ubI : Int) -> LT lbI ubI ->
         (0 bt : BT lt arr lbI lbV ubI ubV) ->
         IO (Dec (Exists (Inside lt arr lbI lbV ubI ubV)))
search = ?a
