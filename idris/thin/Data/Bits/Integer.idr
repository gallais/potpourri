module Data.Bits.Integer

import Data.Bits
import Data.Bool
import Data.So

import Decidable.Equality

%default total

||| This should be far safer than `believe_me` as:
||| 1. we only reduce to `Refl` when x actually equals y
||| 2. we don't expose the implementation so that users can't force reductions in an absurd context
unsafeRefl : DecEq a => {x, y : a} -> x === y
unsafeRefl {x} {y} with (decEq x y)
  _ | Yes eq = eq
  _ | No neq = assert_total $ idris_crash "Equality postulated using unsafeRefl is incorrect"

------------------------------------------------------------------------------
-- Extensional equality
------------------------------------------------------------------------------

infix 6 ~~~
public export
(~~~) : Integer -> Integer -> Type
bs ~~~ cs = (i : Nat) -> testBit bs i === testBit cs i

export
extensionally : {bs, cs : Integer} -> bs ~~~ cs -> bs === cs
extensionally fext = unsafeRefl

------------------------------------------------------------------------------
-- ShiftR properties
------------------------------------------------------------------------------

export
testBitShiftR : (bs : Integer) -> (k : Nat) ->
                (i : Nat) -> testBit (bs `shiftR` k) i === testBit bs (k + i)
testBitShiftR bs k i = unsafeRefl

export
setBitShiftR : (bs : Integer) -> (k : Nat) ->
               (i : Nat) -> k `LTE` i ->
               (setBit bs i) `shiftR` k === setBit (bs `shiftR` k) (minus i k)
setBitShiftR bs k i lte = unsafeRefl

export
clearBitShiftR : (bs : Integer) -> (k : Nat) ->
                 (i : Nat) -> k `LTE` i ->
                 (clearBit bs i) `shiftR` k === clearBit (bs `shiftR` k) (minus i k)
clearBitShiftR bs k i lte = unsafeRefl

------------------------------------------------------------------------------
-- ShiftL properties
------------------------------------------------------------------------------

export
testBit0ShiftL : (bs : Integer) -> (k : Nat) ->
                 testBit (bs `shiftL` S k) Z === False
testBit0ShiftL bs k = unsafeRefl

export
testBitSShiftL : (bs : Integer) -> (k : Nat) -> (i : Nat) ->
                 testBit (bs `shiftL` S k) (S i) === testBit (bs `shiftL` k) i
testBitSShiftL bs k i = unsafeRefl

export
shiftL0 : (bs : Integer) -> (bs `shiftL` 0) === bs
shiftL0 bs = unsafeRefl

export
shiftLR : (bs : Integer) -> (bs `shiftL` 1) `shiftR` 1 === bs
shiftLR bs = unsafeRefl

export
setBit0shiftR : (bs : Integer) -> setBit bs 0 `shiftR` 1 === bs `shiftR` 1
setBit0shiftR bs = unsafeRefl

------------------------------------------------------------------------------
-- And properties
------------------------------------------------------------------------------

export
||| Postulated: conjunction is bitwise on integers
testBitAnd : (bs, cs : Integer) -> (i : Nat) ->
             testBit (bs .&. cs) i === (testBit bs i && testBit cs i)
testBitAnd bs cs i = unsafeRefl

export
shiftRAnd : (bs, cs : Integer) -> (k : Nat) ->
            (bs .&. cs) `shiftR` k === bs `shiftR` k .&. cs `shiftR` k
shiftRAnd bs cs k = extensionally $ \ i =>
  rewrite testBitAnd (bs `shiftR` k) (cs `shiftR` k) i in
  rewrite testBitShiftR bs k i in
  rewrite testBitShiftR cs k i in
  rewrite testBitShiftR (bs .&. cs) k i in
  rewrite testBitAnd bs cs (k + i) in
  Refl

export
andIdempotent : (bs : Integer) -> bs .&. bs === bs
andIdempotent bs = extensionally $ \ i =>
  rewrite testBitAnd bs bs i in
  andSameNeutral (testBit bs i)

------------------------------------------------------------------------------
-- Or properties
------------------------------------------------------------------------------

export
||| Postulated: disjunction is bitwise on integers
testBitOr : (bs, cs : Integer) -> (i : Nat) ->
            testBit (bs .|. cs) i === (testBit bs i || testBit cs i)
testBitOr bs cs i = unsafeRefl

export
shiftROr : (bs, cs : Integer) -> (k : Nat) ->
           (bs .|. cs) `shiftR` k === (bs `shiftR` k .|. cs `shiftR` k)
shiftROr bs cs k = extensionally $ \ i =>
  rewrite testBitOr (bs `shiftR` k) (cs `shiftR` k) i in
  rewrite testBitShiftR bs k i in
  rewrite testBitShiftR cs k i in
  rewrite testBitShiftR (bs .|. cs) k i in
  rewrite testBitOr bs cs (k + i) in
  Refl

export
orIdempotent : (bs : Integer) -> (bs .|. bs) === bs
orIdempotent bs = extensionally $ \ i =>
  rewrite testBitOr bs bs i in
  orSameNeutral (testBit bs i)

------------------------------------------------------------------------------
-- Complement properties
------------------------------------------------------------------------------

export
||| Postulated: complement is bitwise on integers
testBitComplement : (i : Nat) -> (bs : Integer) ->
                    testBit (complement bs) i === not (testBit bs i)
testBitComplement i bs = unsafeRefl

export
complementInvolutive : (bs : Integer) -> complement (complement bs) === bs
complementInvolutive bs = extensionally $ \ i =>
  rewrite testBitComplement i (complement bs) in
  rewrite testBitComplement i bs in
  notInvolutive (testBit bs i)

------------------------------------------------------------------------------
-- Xor properties
------------------------------------------------------------------------------

export
||| Postulated: exclusive-or is bitwise on integers
testBitXor : (bs, cs : Integer) -> (i : Nat) ->
             testBit (bs `xor` cs) i === not (testBit bs i == testBit cs i)
testBitXor bs cs i = unsafeRefl

------------------------------------------------------------------------------
-- Eq properties
------------------------------------------------------------------------------

export
eqReflexive : (bs : Integer) -> (bs == bs) === True
eqReflexive bs = unsafeRefl

equalNatSound : (i, j : Nat) -> i === j -> So (i == j)
equalNatSound Z Z eq = Oh
equalNatSound (S i) (S j) eq = equalNatSound i j (cong pred eq)

export
equalNatComplete : (i, j : Nat) -> So (i == j) -> i === j
equalNatComplete Z Z _ = Refl
equalNatComplete (S i) (S j) hyp = cong S (equalNatComplete i j hyp)

------------------------------------------------------------------------------
-- Bit properties
------------------------------------------------------------------------------

export
bitNonZero : (i : Nat) -> (bit i == 0) === False
bitNonZero i = unsafeRefl

export
bitEquality : (i, j : Nat) -> (bit {a = Integer} i == bit j) === (i == j)
bitEquality i j = case choose (i == j) of
  Left so => rewrite equalNatComplete i j so in
             rewrite eqReflexive (bit j) in
             sym $ soToEq $ equalNatSound j j Refl
  Right soNot => unsafeRefl -- TODO: fix

export
testBitBitSame : (i : Nat) -> testBit {a = Integer} (bit i) i === True
testBitBitSame i =
  rewrite andIdempotent (bit i) in
  rewrite bitNonZero i in
  Refl

------------------------------------------------------------------------------
-- Constant properties
------------------------------------------------------------------------------

export
testBitZeroBits : (i : Nat) -> testBit (zeroBits {a = Integer}) i === False
testBitZeroBits i = unsafeRefl

export
testBitOneBits : (i : Nat) -> testBit (oneBits {a = Integer}) i === True
testBitOneBits i = unsafeRefl

------------------------------------------------------------------------------
-- TestBit properties
------------------------------------------------------------------------------

export
testSetBitSame : (bs : Integer) -> (i : Nat) -> So (testBit (setBit bs i) i)
testSetBitSame bs i =
  rewrite testBitOr bs (bit i) i in
  rewrite testBitBitSame i in
  rewrite orTrueTrue (testBit bs i) in
  Oh

export
testClearBitSame : (bs : Integer) -> (i : Nat) -> So (not $ testBit (clearBit bs i) i)
testClearBitSame bs i = replace {p = So} unsafeRefl Oh -- TODO: bother proving it

export
testSetBitOther : (bs : Integer) -> (i, j : Nat) -> Not (i === j) ->
                  testBit (setBit bs i) j === testBit bs j
testSetBitOther bs i j neq = unsafeRefl

export
testClearBitOther : (bs : Integer) -> (i, j : Nat) -> Not (i === j) ->
                    testBit (clearBit bs i) j === testBit bs j
testClearBitOther bs i j neq = unsafeRefl
