||| Postulated properties of Integer's implementation of the Bits interface

module Data.Bits.Integer.Postulated

import Data.Bits
import Decidable.Equality

%default total

||| This should be far safer than `believe_me` as:
||| 1. we only reduce to `Refl` when x actually equals y
||| 2. we don't expose the implementation so that users
|||    cannot force reductions in an absurd context
unsafeRefl : DecEq a => {x, y : a} -> x === y
unsafeRefl {x} {y} with (decEq x y)
  _ | Yes eq = eq
  _ | No neq = assert_total $ idris_crash "Equality postulated using unsafeRefl is incorrect"

------------------------------------------------------------------------------
-- Extensional equality
------------------------------------------------------------------------------

infix 6 ~~~

||| testBit-induced pointwise equality of arbitrary precision integers
public export
(~~~) : Integer -> Integer -> Type
bs ~~~ cs = (i : Nat) -> testBit bs i === testBit cs i

||| Postulated extensionality principle:
||| from pointwise equality we can conclude propositional equality
export
extensionally : {bs, cs : Integer} -> bs ~~~ cs -> bs === cs
extensionally fext = unsafeRefl


------------------------------------------------------------------------------
-- Postulated properties
------------------------------------------------------------------------------

||| If we shift an integer whose bit pattern is bₙ⋯b₀
||| to the right by k, we get bₙ₋ₖ⋯bₖ.
||| Correspondingly, testing the bit i on the shifted integer
||| amounts to testing the bit (k + i) on the original one.
export
testBitShiftR : (bs : Integer) -> (k : Nat) ->
  (i : Nat) -> testBit (bs `shiftR` k) i === testBit bs (k + i)
testBitShiftR bs k i = unsafeRefl

||| If we shift an integer whose bit pattern is bₙ⋯b₀
||| to the left by k, we get bₙ⋯b₀0⋯0.
|||                               ^^^ k zeros
||| Correspondingly, if k is non-zero then testing the bit 0
||| is guaranteed to return 0.
export
testBit0ShiftL : (bs : Integer) -> (k : Nat) ->
  testBit (bs `shiftL` S k) Z === False
testBit0ShiftL bs k = unsafeRefl

||| If we shift an integer whose bit pattern is bₙ⋯b₀
||| to the left by k, we get bₙ⋯b₀0⋯0.
|||                               ^^^ k zeros
||| Correspondingly, if k is non-zero then testing the bit (S i)
||| on the shifted integer amounts to testing the bit i on the
||| integer shifted by (k-1).
export
testBitSShiftL : (bs : Integer) -> (k : Nat) -> (i : Nat) ->
  testBit (bs `shiftL` S k) (S i) === testBit (bs `shiftL` k) i
testBitSShiftL bs k i = unsafeRefl

||| If we shift an integer whose bit pattern is bₙ⋯b₀
||| to the left by k, we get bₙ⋯b₀0⋯0.
|||                               ^^^ k zeros
||| Correspondingly, shifting by 0 is the identity.
export
shiftL0 : (bs : Integer) -> (bs `shiftL` 0) === bs
shiftL0 bs = unsafeRefl

||| Conjunction is bitwise on integers
export
testBitAnd : (bs, cs : Integer) -> (i : Nat) ->
  testBit (bs .&. cs) i === (testBit bs i && testBit cs i)
testBitAnd bs cs i = unsafeRefl

||| Disjunction is bitwise on integers
export
testBitOr : (bs, cs : Integer) -> (i : Nat) ->
  testBit (bs .|. cs) i === (testBit bs i || testBit cs i)
testBitOr bs cs i = unsafeRefl

||| If we set the bit i of an integer whose bit pattern is bₙ⋯b₀,
||| we get bₙ⋯bᵢ₊₁1bᵢ₋₁⋯b₀.
||| Correspondingly, testing a bit j different from i
||| amounts to testing bit j on the original integer.
export
testSetBitOther : (bs : Integer) -> (i, j : Nat) -> Not (i === j) ->
  testBit (setBit bs i) j === testBit bs j
testSetBitOther bs i j neq = unsafeRefl

||| Complement is bitwise on integers
export
testBitComplement : (bs : Integer) -> (i : Nat) ->
  testBit (complement bs) i === not (testBit bs i)
testBitComplement bs i = unsafeRefl

||| The integer whose bit pattern is 10⋯0 is non-zero
|||                                   ^^^ i-1 zeros
export
bitNonZero : (i : Nat) -> (bit i == 0) === False
bitNonZero i = unsafeRefl
