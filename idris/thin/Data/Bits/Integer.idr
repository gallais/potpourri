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
-- And properties
------------------------------------------------------------------------------

export
||| Postulated: conjunction is bitwise on integers
testBitAnd : (i : Nat) -> (bs, cs : Integer) ->
             testBit (bs .&. cs) i === (testBit bs i && testBit cs i)
testBitAnd i bs cs = unsafeRefl

export
||| Postulated: conjunction is idempotent on integers
andIdempotent : (bs : Integer) -> bs .&. bs === bs
andIdempotent bs = extensionally $ \ i =>
  rewrite testBitAnd i bs bs in
  andSameNeutral (testBit bs i)

------------------------------------------------------------------------------
-- Or properties
------------------------------------------------------------------------------

export
||| Postulated: disjunction is bitwise on integers
testBitOr : (i : Nat) -> (bs, cs : Integer) ->
            testBit (bs .|. cs) i === (testBit bs i || testBit cs i)
testBitOr i bs cs = unsafeRefl

export
||| Postulated: conjunction is idempotent on integers
orIdempotent : (bs : Integer) -> (bs .|. bs) === bs
orIdempotent bs = extensionally $ \ i =>
  rewrite testBitOr i bs bs in
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
testBitXor : (i : Nat) -> (bs, cs : Integer) ->
             testBit (bs `xor` cs) i === not (testBit bs i == testBit cs i)
testBitXor i bs cs = unsafeRefl

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
testSetBitSame : (i : Nat) -> (bs : Integer) -> So (testBit (setBit bs i) i)
testSetBitSame i bs =
  rewrite testBitOr i bs (bit i) in
  rewrite testBitBitSame i in
  rewrite orTrueTrue (testBit bs i) in
  Oh

export
testClearBitSame : (i : Nat) -> (bs : Integer) -> So (not $ testBit (clearBit bs i) i)
testClearBitSame i bs = replace {p = So} unsafeRefl Oh -- TODO: bother proving it

export
testSetBitOther : (i, j : Nat) -> Not (i === j) ->
                  (bs : Integer) -> testBit (setBit bs i) j === testBit bs j
testSetBitOther i j neq bs = unsafeRefl

export
testClearBitOther : (i, j : Nat) -> Not (i === j) ->
                    (bs : Integer) -> testBit (clearBit bs i) j === testBit bs j
testClearBitOther i j neq bs = unsafeRefl
