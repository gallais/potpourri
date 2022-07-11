||| Postulated properties of Data.Bits for Integer
||| NB: some of these are probably provable

module Data.Bits.Integer.Postulated

import Data.Bits
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
-- Postulated properties
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
||| Postulated: conjunction is bitwise on integers
testBitAnd : (bs, cs : Integer) -> (i : Nat) ->
             testBit (bs .&. cs) i === (testBit bs i && testBit cs i)
testBitAnd bs cs i = unsafeRefl

export
||| Postulated: disjunction is bitwise on integers
testBitOr : (bs, cs : Integer) -> (i : Nat) ->
            testBit (bs .|. cs) i === (testBit bs i || testBit cs i)
testBitOr bs cs i = unsafeRefl

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

export
||| Postulated: complement is bitwise on integers
testBitComplement : (bs : Integer) -> (i : Nat) ->
                    testBit (complement bs) i === not (testBit bs i)
testBitComplement bs i = unsafeRefl

export
bitNonZero : (i : Nat) -> (bit i == 0) === False
bitNonZero i = unsafeRefl

export
||| Postulated: exclusive-or is bitwise on integers
testBitXor : (bs, cs : Integer) -> (i : Nat) ->
             testBit (bs `xor` cs) i === not (testBit bs i == testBit cs i)
testBitXor bs cs i = unsafeRefl

export
eqReflexive : (bs : Integer) -> (bs == bs) === True
eqReflexive bs = unsafeRefl

export
eqSound : {bs, cs : Integer} -> So (bs == cs) -> bs === cs
eqSound p = unsafeRefl
