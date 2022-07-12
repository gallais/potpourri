module Data.Bits.Integer

import Data.Bits
import public Data.Bits.Integer.Postulated
import Data.Bool
import Data.So
import Data.Nat.Order

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
-- And properties
------------------------------------------------------------------------------

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
-- ShiftL properties
------------------------------------------------------------------------------

export
shiftLSR : (bs : Integer) -> (k : Nat) -> (bs `shiftL` S k) `shiftR` 1 === bs `shiftL` k
shiftLSR bs k = extensionally $ \ i => Calc $
  |~ testBit ((bs `shiftL` S k) `shiftR` 1) i
  ~~ testBit (bs `shiftL` S k) (S i) ...( testBitShiftR (bs `shiftL` S k) 1 i )
  ~~ testBit (bs `shiftL` k) i       ...( testBitSShiftL bs k i )

export
shiftLR : (bs : Integer) -> (bs `shiftL` 1) `shiftR` 1 === bs
shiftLR bs = Calc $
  |~ (bs `shiftL` 1) `shiftR` 1
  ~~ bs `shiftL` 0              ...( shiftLSR bs 0 )
  ~~ bs                         ...( shiftL0 bs )

export
setBit0ShiftR : (bs : Integer) -> setBit bs 0 `shiftR` 1 === bs `shiftR` 1
setBit0ShiftR bs = extensionally $ \ i => Calc $
  |~ testBit (setBit bs 0 `shiftR` 1) i
  ~~ testBit (setBit bs 0) (S i)        ...( testBitShiftR (setBit bs 0) 1 i )
  ~~ testBit bs (S i)                   ...( testSetBitOther bs 0 (S i) absurd )
  ~~ testBit (bs `shiftR` 1) i          ...( sym $ testBitShiftR bs 1 i )

export
clearBit0ShiftR : (bs : Integer) -> clearBit bs 0 `shiftR` 1 === bs `shiftR` 1
clearBit0ShiftR bs = extensionally $ \ i => Calc $
  |~ testBit (clearBit bs 0 `shiftR` 1) i
  ~~ testBit (clearBit bs 0) (S i)        ...( testBitShiftR (clearBit bs 0) 1 i )
  ~~ testBit bs (S i)                     ...( testClearBitOther bs 0 (S i) absurd )
  ~~ testBit (bs `shiftR` 1) i            ...( sym $ testBitShiftR bs 1 i )

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

export
shiftRBitS : (i : Nat) -> bit (S i) `shiftR` 1 === the Integer (bit i)
shiftRBitS i = shiftLSR 1 i

------------------------------------------------------------------------------
-- Ones properties
------------------------------------------------------------------------------

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

export
testBitZeroBits : (i : Nat) -> testBit (zeroBits {a = Integer}) i === False
testBitZeroBits i = Calc $
  |~ testBit (the Integer zeroBits) i
  ~~ not (testBit (the Integer oneBits) i) ...( testBitComplement oneBits i )
  ~~ False                                 ...( cong not (testBitOneBits i) )

export
zeroBitsShiftL : (k : Nat) -> zeroBits {a = Integer} `shiftL` k === Bits.zeroBits
zeroBitsShiftL 0 = shiftL0 zeroBits
zeroBitsShiftL (S k) = extensionally $ \case
  0 => testBit0ShiftL zeroBits k
  S i => Calc $
    |~ testBit (zeroBits {a = Integer} `shiftL` S k) (S i)
    ~~ testBit (zeroBits {a = Integer} `shiftL` k) i       ...( testBitSShiftL zeroBits k i )
    ~~ testBit (zeroBits {a = Integer}) i                  ...( cong (`testBit` i) (zeroBitsShiftL k) )
    ~~ False                                               ...( testBitZeroBits i )
    ~~ testBit (zeroBits {a = Integer}) (S i)              ...( sym (testBitZeroBits (S i)) )

------------------------------------------------------------------------------
-- Or properties
------------------------------------------------------------------------------

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

export
orZeroBitsRightIdentity : (bs : Integer) -> (bs .|. Bits.zeroBits) === bs
orZeroBitsRightIdentity bs = extensionally $ \ i =>
  rewrite testBitOr bs zeroBits i in
  rewrite testBitZeroBits i in
  rewrite orFalseNeutral (testBit bs i) in
  Refl

export
orZeroBitsLeftIdentity : (bs : Integer) -> (Bits.zeroBits .|. bs) === bs
orZeroBitsLeftIdentity bs = extensionally $ \ i =>
  rewrite testBitOr zeroBits bs i in
  rewrite testBitZeroBits i in
  Refl

------------------------------------------------------------------------------
-- Complement properties
------------------------------------------------------------------------------

export
complementInvolutive : (bs : Integer) -> complement (complement bs) === bs
complementInvolutive bs = extensionally $ \ i =>
  rewrite testBitComplement (complement bs) i in
  rewrite testBitComplement bs i in
  notInvolutive (testBit bs i)

------------------------------------------------------------------------------
-- Eq properties
------------------------------------------------------------------------------

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
testOneS : (i : Nat) -> testBit (the Integer 1) (S i) === False
testOneS 0 = Refl
testOneS (S i) = Calc $
  |~ testBit 1 (2 + i)
  ~~ testBit (the Integer 1 `shiftR` 1) (S i) ...( sym $ testBitShiftR 1 1 (S i) )
  ~~ testBit 0 (S i) ...( Refl )
  ~~ False ...( testBitZeroBits (S i) )

export
testBitBitSame : (i : Nat) -> testBit {a = Integer} (bit i) i === True
testBitBitSame i =
  rewrite andIdempotent (bit i) in
  rewrite bitNonZero i in
  Refl

export
testBitBitOther : (i, j : Nat) -> Not (i === j) ->
                  testBit {a = Integer} (bit i) j === False
testBitBitOther 0 0 neq = absurd (neq Refl)
testBitBitOther 0 (S j) neq = Calc $
  |~ testBit (the Integer 1 `shiftL` 0) (S j)
  ~~ testBit 1 (S j)  ...( cong (`testBit` S j) (shiftL0 1) )
  ~~ False            ...( testOneS j )
testBitBitOther (S i) 0 neq = testBit0ShiftL 1 i
testBitBitOther (S i) (S j) neq = Calc $
  |~ testBit (the Integer 1 `shiftL` S i) (S j)
  ~~ testBit (the Integer $ bit i) j  ...( testBitSShiftL 1 i j )
  ~~ False                            ...( testBitBitOther i j (neq . cong S) )

------------------------------------------------------------------------------
-- Constant properties
------------------------------------------------------------------------------

notSoToSoNot : {b : Bool} -> Not (So b) -> So (not b)
notSoToSoNot {b = False} p = Oh
notSoToSoNot {b = True} notSo = absurd (notSo Oh)

export
bitInjective : (i, j : Nat) -> (bit {a = Integer} i == bit j) === (i == j)
bitInjective i j = case choose (i == j) of
  Left so => rewrite equalNatComplete i j so in
             rewrite eqReflexive (bit j) in
             sym $ soToEq $ equalNatSound j j Refl
  Right soNot => Calc $
    |~ (the Integer (bit i) == bit j)
    ~~ not (not (the Integer (bit i) == bit j)) ...( sym $ notInvolutive ? )
    ~~ False                                    ...( cong not (soToEq (aux soNot)) )
    ~~ not (not (equalNat i j))                 ...( sym $ cong not (soToEq soNot) )
    ~~ (i == j)                                 ...( notInvolutive ? )

  where

  aux : So (not (i == j)) -> So (not $ the Integer (bit i) == bit j)
  aux soNot = notSoToSoNot $ \ so => absurd $ Calc $
    let neq : Not (j === i) = soNotToNotSo soNot . equalNatSound i j . symmetric in
    |~ True
    ~~ testBit (the Integer $ bit i) i ...( sym $ testBitBitSame i )
    ~~ testBit (the Integer $ bit j) i ...( cong (`testBit` i) (eqSound so) )
    ~~ False                           ...( testBitBitOther j i neq )

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
