||| Definitions using Integer's implementation of the Bits interface
||| and proofs of various properties.

module Data.Bits.Integer

import Data.Bits
import public Data.Bits.Integer.Postulated
import Data.Bool
import Data.So
import Data.Nat.Order

import Syntax.PreorderReasoning

-- The Syntax.PreorderReasoning module ships as part of Idris 2's standard
-- library. It defines the preorder-reasoning syntax which allows us write:
--     |~ x
--     ~~ y ...( eq1 )
--     ~~ z ...( eq2 )
-- to derive (x === z) by combining eq1 of type (x === y) and
-- eq2 of type (y === z)


%default total

------------------------------------------------------------------------------
-- Additional functions
------------------------------------------------------------------------------

||| cofull takes a natural number n and returns an integer
||| whose bit pattern is
|||
|||   vv infinitely many leading ones
|||   ⋯10⋯0
|||     ^^^ n zeros
public export
cofull : Nat -> Integer
cofull n = oneBits `shiftL` n

||| full takes a natural number n and returns an integer
||| whose bit pattern is n ones
public export
full : Nat -> Integer
full n = complement (cofull n)

||| cons takes a bit b and an integer whose bit pattern is bₙ⋯b₀ and
||| returns an integer whose bit pattern is bₙ⋯b₀b
public export
cons : Bool -> Integer -> Integer
cons b bs = let bs0 = bs `shiftL` 1 in
            if b then (bs0 `setBit` 0) else bs0

------------------------------------------------------------------------------
-- And properties
------------------------------------------------------------------------------

||| shiftR distributes over conjunction
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

||| conjunction is idempotent
export
andIdempotent : (bs : Integer) -> bs .&. bs === bs
andIdempotent bs = extensionally $ \ i =>
  rewrite testBitAnd bs bs i in
  andSameNeutral (testBit bs i)

------------------------------------------------------------------------------
-- ShiftL properties
------------------------------------------------------------------------------

||| (`shiftR` 1) after (`shiftL` S k) amounts to (`shiftL` k)
export
shiftLSR : (bs : Integer) -> (k : Nat) -> (bs `shiftL` S k) `shiftR` 1 === bs `shiftL` k
shiftLSR bs k = extensionally $ \ i => Calc $
  |~ testBit ((bs `shiftL` S k) `shiftR` 1) i
  ~~ testBit (bs `shiftL` S k) (S i) ...( testBitShiftR (bs `shiftL` S k) 1 i )
  ~~ testBit (bs `shiftL` k) i       ...( testBitSShiftL bs k i )

||| shiftR is a right-inverse to shiftL
export
shiftLR : (bs : Integer) -> (bs `shiftL` 1) `shiftR` 1 === bs
shiftLR bs = Calc $
  |~ (bs `shiftL` 1) `shiftR` 1
  ~~ bs `shiftL` 0              ...( shiftLSR bs 0 )
  ~~ bs                         ...( shiftL0 bs )

||| (`shiftR` 1) cancels (`setBit‵ 0) because it drops the last digit
export
setBit0ShiftR : (bs : Integer) -> setBit bs 0 `shiftR` 1 === bs `shiftR` 1
setBit0ShiftR bs = extensionally $ \ i => Calc $
  |~ testBit (setBit bs 0 `shiftR` 1) i
  ~~ testBit (setBit bs 0) (S i)        ...( testBitShiftR (setBit bs 0) 1 i )
  ~~ testBit bs (S i)                   ...( testSetBitOther bs 0 (S i) absurd )
  ~~ testBit (bs `shiftR` 1) i          ...( sym $ testBitShiftR bs 1 i )

||| (`shiftL` k) is injective (proven by induction on k)
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
-- Bit properties
------------------------------------------------------------------------------

||| Right-shifting an integer whose bit pattern is
||| 10⋯0 by 1 yields 10⋯0 (for a non-zero i)
|||  ^^^ i zeros      ^^^ i-1 zeros
export
shiftRBitS : (i : Nat) -> bit (S i) `shiftR` 1 === the Integer (bit i)
shiftRBitS i = shiftLSR 1 i

------------------------------------------------------------------------------
-- Ones properties
------------------------------------------------------------------------------

||| Testing any bit of the integer whose bit pattern is ⋯1 is inevitably 1
export
testBitOneBits : (i : Nat) -> testBit (oneBits {a = Integer}) i === True
testBitOneBits 0 = Refl
testBitOneBits (S i) = Calc $
  |~ testBit (the Integer oneBits) (S i)
  ~~ testBit (the Integer oneBits `shiftR` 1) i ...( sym $ testBitShiftR oneBits 1 i )
  ~~ True                                       ...( testBitOneBits i )

------------------------------------------------------------------------------
-- Zeros properties
------------------------------------------------------------------------------

||| Testing any bit of the integer whose bit pattern is 0 is inevitably 0
export
testBitZeroBits : (i : Nat) -> testBit (zeroBits {a = Integer}) i === False
testBitZeroBits i = Calc $
  |~ testBit (the Integer zeroBits) i
  ~~ not (testBit (the Integer oneBits) i) ...( testBitComplement oneBits i )
  ~~ False                                 ...( cong not (testBitOneBits i) )

------------------------------------------------------------------------------
-- Or properties
------------------------------------------------------------------------------

||| shiftR distributes over disjunction
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

||| Disjunction is idempotent
export
orIdempotent : (bs : Integer) -> (bs .|. bs) === bs
orIdempotent bs = extensionally $ \ i =>
  rewrite testBitOr bs bs i in
  orSameNeutral (testBit bs i)

||| The integer whose bit pattern is 0 is a right neutral for disjunction
export
orZeroBitsRightIdentity : (bs : Integer) -> (bs .|. Bits.zeroBits) === bs
orZeroBitsRightIdentity bs = extensionally $ \ i =>
  rewrite testBitOr bs zeroBits i in
  rewrite testBitZeroBits i in
  rewrite orFalseNeutral (testBit bs i) in
  Refl

||| The integer whose bit pattern is 0 is a left neutral for disjunction
export
orZeroBitsLeftIdentity : (bs : Integer) -> (Bits.zeroBits .|. bs) === bs
orZeroBitsLeftIdentity bs = extensionally $ \ i =>
  rewrite testBitOr zeroBits bs i in
  rewrite testBitZeroBits i in
  Refl

------------------------------------------------------------------------------
-- Complement properties
------------------------------------------------------------------------------

||| Complement is involutive
export
complementInvolutive : (bs : Integer) -> complement (complement bs) === bs
complementInvolutive bs = extensionally $ \ i =>
  rewrite testBitComplement (complement bs) i in
  rewrite testBitComplement bs i in
  notInvolutive (testBit bs i)

------------------------------------------------------------------------------
-- Eq properties
------------------------------------------------------------------------------

||| Boolean equality of natural numbers is sound
equalNatSound : (i, j : Nat) -> i === j -> So (i == j)
equalNatSound Z Z eq = Oh
equalNatSound (S i) (S j) eq = equalNatSound i j (cong pred eq)

||| Boolean Equality of natural numbers is complete
export
equalNatComplete : (i, j : Nat) -> So (i == j) -> i === j
equalNatComplete Z Z _ = Refl
equalNatComplete (S i) (S j) hyp = cong S (equalNatComplete i j hyp)

------------------------------------------------------------------------------
-- Bit properties
------------------------------------------------------------------------------

||| Testing any bit but the 0th one for the Integer 1 yields 0
export
testOneS : (i : Nat) -> testBit (the Integer 1) (S i) === False
testOneS 0 = Refl
testOneS (S i) = Calc $
  |~ testBit 1 (2 + i)
  ~~ testBit (the Integer 1 `shiftR` 1) (S i) ...( sym $ testBitShiftR 1 1 (S i) )
  ~~ testBit 0 (S i) ...( Refl )
  ~~ False ...( testBitZeroBits (S i) )

||| Testing the ith bit of the integer whose bit pattern is
||| 10⋯0 yields 1
|||  ^^^ i-1 zeros
export
testBitBitSame : (i : Nat) -> testBit {a = Integer} (bit i) i === True
testBitBitSame i =
  rewrite andIdempotent (bit i) in
  rewrite bitNonZero i in
  Refl

------------------------------------------------------------------------------
-- Constant properties
------------------------------------------------------------------------------

||| Auxiliary lemma, should probably be moved to Idris 2's standard library
notSoToSoNot : {b : Bool} -> Not (So b) -> So (not b)
notSoToSoNot {b = False} p = Oh
notSoToSoNot {b = True} notSo = absurd (notSo Oh)

------------------------------------------------------------------------------
-- (Co)Full properties
------------------------------------------------------------------------------

||| cofull k is an integer whose bit pattern is
||| vv infinitely many ones
||| ⋯10⋯0
|||   ^^^ k zeros
||| and so testing the ith bit amounts to testing
||| whether i is greater or equal to k
export
testBitCofull : (k : Nat) -> (i : Nat) ->
                testBit (cofull k) i === not (i `lt` k)
testBitCofull 0 i = testBitOneBits i
testBitCofull (S k) 0 = testBit0ShiftL oneBits k
testBitCofull (S k) (S i)
  = rewrite testBitSShiftL oneBits k i in
    testBitCofull k i

||| full k is an integer whose bit pattern is 1⋯1
|||                                           ^^^ k ones
||| and so testing the ith bit amounts to testing
||| whether i is less than k
export
testBitFull : (k : Nat) -> (i : Nat) -> testBit (full k) i === (i `lt` k)
testBitFull k i
  = rewrite testBitComplement (cofull k) i in
    rewrite testBitCofull k i in
    notInvolutive (i `lt` k)

||| full k is an integer whose bit pattern is 1⋯1
|||                                           ^^^ k ones
||| and so, for a non-zero k, a right shift gets us full (k - 1)
export
shiftRFull : (k : Nat) -> full (S k) `shiftR` 1 === full k
shiftRFull k = extensionally $ \ i =>
  rewrite testBitShiftR (full (S k)) 1 i in
  rewrite testBitFull k i in
  testBitFull (S k) (S i)

------------------------------------------------------------------------------
-- TestBit properties
------------------------------------------------------------------------------

||| Testing a bit that was just set will necessarily return 1
export
testSetBitSame : (bs : Integer) -> (i : Nat) -> So (testBit (setBit bs i) i)
testSetBitSame bs i =
  rewrite testBitOr bs (bit i) i in
  rewrite testBitBitSame i in
  rewrite orTrueTrue (testBit bs i) in
  Oh

------------------------------------------------------------------------------
-- Cons properties
------------------------------------------------------------------------------

||| Testing the Oth bit on (cons b bs) will inevitably return b
export
testBit0Cons : (b : Bool) -> (bs : Integer) ->
               testBit (cons b bs) 0 === b
testBit0Cons True bs = soToEq $ testSetBitSame (bs `shiftL` 1) 0
testBit0Cons False bs = testBit0ShiftL bs 0

||| Testing the the bit (S i) on (cons b bs) amounts to testing
||| the bit i on the original integer bs.
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

||| A single right-shift cancels cons
export
consShiftR : (b : Bool) -> (bs : Integer) ->
             (cons b bs) `shiftR` 1 === bs
consShiftR True bs =  Calc $
  |~ cons True bs `shiftR` 1
  ~~ (bs `shiftL` 1) `shiftR` 1 ...( setBit0ShiftR (bs `shiftL` 1) )
  ~~ bs                         ...( shiftLR bs )
consShiftR False bs = Calc $
  |~ cons False bs `shiftR` 1
  ~~ bs                        ...( shiftLR bs )

||| Cons is injective
export
consInjective : (b : Bool) -> (bs, cs : Integer) ->
                cons b bs === cons b cs -> bs === cs
consInjective b bs cs eq = Calc $
  |~ bs
  ~~ cons b bs `shiftR` 1 ...( sym $ consShiftR b bs )
  ~~ cons b cs `shiftR` 1 ...( cong (`shiftR` 1) eq )
  ~~ cs                   ...( consShiftR b cs )
