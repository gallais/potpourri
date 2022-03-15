module Data.Bits.Integer

import Data.Bits
import Data.Bool
import Data.So
import Data.Nat.Order

import Decidable.Equality

import Syntax.PreorderReasoning

%default total


------------------------------------------------------------------------------
-- Additional functions
------------------------------------------------------------------------------

||| cofull takes a natural number k and returns an integer whose bit pattern is
||| k zeros followed by ones
public export
cofull : Nat -> Integer
cofull k = oneBits `shiftL` k

||| full takes a natural number k and returns an integer whose bit pattern is
||| k ones followed by zeros
public export
full : Nat -> Integer
full k = complement (cofull k)

||| cons takes a bit and an integer and returns an integer whose bit pattern
||| is that bit followed by the original integer
public export
cons : Bool -> Integer -> Integer
cons b bs = ifThenElse b (`setBit` 0) id (bs `shiftL` 1)

------------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------------


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
setBit0ShiftR : (bs : Integer) -> setBit bs 0 `shiftR` 1 === bs `shiftR` 1
setBit0ShiftR bs = unsafeRefl

export
clearBit0ShiftR : (bs : Integer) -> clearBit bs 0 `shiftR` 1 === bs `shiftR` 1
clearBit0ShiftR bs = unsafeRefl

export
shiftLInjective : (bs, cs : Integer) -> (k : Nat) ->
                  bs `shiftL` k === cs `shiftL` k -> bs === cs
shiftLInjective bs cs 0 eq = Calc $
  |~ bs
  ~~ bs `shiftL` 0 ...( sym $ shiftL0 bs )
  ~~ cs `shiftL` 0 ...( eq )
  ~~ cs            ...( shiftL0 cs )
shiftLInjective bs cs (S k) eq
  = shiftLInjective bs cs k
  $ extensionally $ \ i => Calc $
  |~ testBit (bs `shiftL` k) i
  ~~ testBit (bs `shiftL` S k) (S i) ...( sym $ testBitSShiftL bs k i )
  ~~ testBit (cs `shiftL` S k) (S i) ...( cong (\ bs => testBit bs (S i)) eq )
  ~~ testBit (cs `shiftL` k) i       ...( testBitSShiftL cs k i )

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
testBitComplement : (bs : Integer) -> (i : Nat) ->
                    testBit (complement bs) i === not (testBit bs i)
testBitComplement bs i = unsafeRefl

export
complementInvolutive : (bs : Integer) -> complement (complement bs) === bs
complementInvolutive bs = extensionally $ \ i =>
  rewrite testBitComplement (complement bs) i in
  rewrite testBitComplement bs i in
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
-- (Co)Full properties
------------------------------------------------------------------------------

export
testBitCofull : (k : Nat) -> (i : Nat) -> testBit (cofull k) i === not (i `lt` k)
testBitCofull 0 i = testBitOneBits i
testBitCofull (S k) 0 = testBit0ShiftL oneBits k
testBitCofull (S k) (S i)
  = rewrite testBitSShiftL oneBits k i in
    testBitCofull k i

export
testBitFull : (k : Nat) -> (i : Nat) -> testBit (full k) i === (i `lt` k)
testBitFull k i
  = rewrite testBitComplement (cofull k) i in
    rewrite testBitCofull k i in
    notInvolutive (i `lt` k)

export
shiftRFull : (k : Nat) -> full (S k) `shiftR` 1 === full k
shiftRFull k = extensionally $ \ i =>
  rewrite testBitShiftR (full (S k)) 1 i in
  rewrite testBitFull k i in
  testBitFull (S k) (S i)

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


------------------------------------------------------------------------------
-- Cons properties
------------------------------------------------------------------------------

export
testBit0Cons : (b : Bool) -> (bs : Integer) -> testBit (cons b bs) 0 === b
testBit0Cons True bs = soToEq $ testSetBitSame (bs `shiftL` 1) 0
testBit0Cons False bs = testBit0ShiftL bs 0

export
testBitSCons : (b : Bool) -> (bs : Integer) -> (i : Nat) ->
               testBit (cons b bs) (S i) === testBit bs i
testBitSCons True bs i = Calc $
  |~ testBit (cons True bs) (S i)
  ~~ testBit (bs `shiftL` 1) (S i) ...( testSetBitOther (bs `shiftL` 1) 0 (S i) absurd )
  ~~ testBit (bs `shiftL` 0) i     ...( testBitSShiftL bs 0 i )
  ~~ testBit bs i                  ...( cong (\ bs => testBit bs i) (shiftL0 bs) )
testBitSCons False bs i = Calc $
  |~ testBit (cons False bs) (S i)
  ~~ testBit (bs `shiftL` 0) i     ...( testBitSShiftL bs 0 i )
  ~~ testBit bs i                  ...( cong (\ bs => testBit bs i) (shiftL0 bs) )

export
consShiftR : (b : Bool) -> (bs : Integer) -> (cons b bs) `shiftR` 1 === bs
consShiftR True bs =  Calc $
  |~ cons True bs `shiftR` 1
  ~~ (bs `shiftL` 1) `shiftR` 1 ...( setBit0ShiftR (bs `shiftL` 1) )
  ~~ bs                         ...( shiftLR bs )
consShiftR False bs = Calc $
  |~ cons False bs `shiftR` 1
  ~~ bs                        ...( shiftLR bs )

export
consInjective : (b : Bool) -> (bs, cs : Integer) ->
                cons b bs === cons b cs -> bs === cs
consInjective b bs cs eq = Calc $
  |~ bs
  ~~ cons b bs `shiftR` 1 ...( sym $ consShiftR b bs )
  ~~ cons b cs `shiftR` 1 ...( cong (`shiftR` 1) eq )
  ~~ cs                   ...( consShiftR b cs )
