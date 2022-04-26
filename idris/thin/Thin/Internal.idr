||| This is the low-level stuff used to implement Thin.
||| The even lower level (sometimes unsafe) results are in Data.Bits.Integer

module Thin.Internal

import Data.Bool
import Data.Bits
import Data.Bits.Integer
import Data.DPair
import Data.Nat
import Data.SnocList
import Data.SnocList.AtIndex

%default total

------------------------------------------------------------------------------
-- TODO: move to stdlib
------------------------------------------------------------------------------

export
irrelevantSo : (0 p, q : So b) -> p === q
irrelevantSo Oh Oh = Refl

------------------------------------------------------------------------------
-- Thinning relation
------------------------------------------------------------------------------

||| Inductive relation characterising when a pair (i, bs) defines a thinning
||| @ sx is the small end of the thinning
||| @ sy is the big end of the thinning
||| @ i  is the size of the big end of the thinning
||| @ bs is an integer but we are only interested in its first @i bits.
||| Each bit in bs indicates whether the associated value in sy is kept in sx
||| For instance: Thinning 2 [01] [<y] [<x,y] because:
|||   i.   2 is the size of [01] (and [<x,y])
|||   ii.  [01] describes [<y] as [<x,y] where x was discarded and y kept
public export
data Thinning : (i : Nat) -> (bs : Integer) -> (sx, sy : SnocList a) -> Type where
  ||| A 0-bits long thinning is a thinning between empty lists
  Done : Thinning Z 0 [<] [<]
  ||| If the last bit of interest is set then the snoclist's head is kept
  Keep : Thinning i (bs `shiftR` 1) sx sy -> (0 x : a) ->
         {auto 0 b  : So (      testBit bs Z)} ->
         Thinning (S i) bs (sx :< x) (sy :< x)
  ||| If the last bit of interest is not set then the snoclist's head is thrown out
  Drop : Thinning i (bs `shiftR` 1) sx sy -> (0 x : a) ->
         {auto 0 nb : So (not $ testBit bs Z)} ->
         Thinning (S i) bs sx        (sy :< x)

------------------------------------------------------------------------------
-- Properties of Thinning
------------------------------------------------------------------------------

export
irrelevantSize : Thinning i bs sa sx -> Thinning j cs sb sx -> i === j
irrelevantSize Done Done = Refl
irrelevantSize (Keep thl x) (Keep thr x) = cong S (irrelevantSize thl thr)
irrelevantSize (Keep thl x) (Drop thr x) = cong S (irrelevantSize thl thr)
irrelevantSize (Drop thl x) (Keep thr x) = cong S (irrelevantSize thl thr)
irrelevantSize (Drop thl x) (Drop thr x) = cong S (irrelevantSize thl thr)

||| The thinning relation is a mere validation relation and thus entirely
||| characterised by its indices. Consequently its proofs are irrelevant.
export
irrelevantThinning : (th1, th2 : Thinning i bs sx sy) -> th1 === th2
irrelevantThinning Done Done = Refl
irrelevantThinning (Keep th1 x {b = b1}) (Keep th2 x {b = b2})
  = cong2 (\ th, b => Keep th x {b}) (irrelevantThinning th1 th2) (irrelevantSo b1 b2)
irrelevantThinning (Drop th1 x {nb = nb1}) (Drop th2 x {nb = nb2})
  = cong2 (\ th, nb => Drop th x {nb}) (irrelevantThinning th1 th2) (irrelevantSo nb1 nb2)
irrelevantThinning (Keep th1 x {b = b1}) (Drop th2 x {nb = nb2})
  = void (soNotToNotSo nb2 b1)
irrelevantThinning (Drop th1 x {nb = nb1}) (Keep th2 x {b = b2})
  = void (soNotToNotSo nb1 b2)

export
none : (sy : SnocList a) -> Thinning (length sy) Bits.zeroBits [<] sy
none [<] = Done
none (sy :< y) =
  let 0 nb = eqToSo (cong not $ testBitZeroBits (S $ length sy)) in
  Drop (none sy) y

export
ones : (sx : SnocList a) -> Thinning (length sx) (full $ length sx) sx sx
ones [<] = Done
ones (sx :< x) =
  let 0 nb = eqToSo (testBitFull (S (length sx)) Z) in
  Keep (rewrite shiftRFull (length sx) in ones sx) x

-- We need to public export so that `fst (meet th ph)` computes at the type level.
-- These are all runtime irrelevant though so their behaviour does not matter.
public export
meet : Thinning i bs sxl sx -> Thinning i cs sxr sx ->
         Exists $ \ sxlr => Thinning i (bs .&. cs) sxlr sx
meet Done Done = Evidence ? Done
meet (Keep thl x @{bl}) (Keep thr x @{br}) =
  let ih = meet thl thr in
  let 0 b : So (testBit (bs .&. cs) 0)
      = rewrite testBitAnd bs cs 0 in
        andSo (bl, br)
  in Evidence (ih .fst :< x) (Keep (rewrite shiftRAnd bs cs 1 in ih .snd) x)
meet (Keep thl x) (Drop thr x @{nbr}) =
  let ih = meet thl thr in
  let 0 nb : So (not $ testBit (bs .&. cs) 0)
      = rewrite testBitAnd bs cs 0 in
        let eq = notAndIsOr (testBit bs 0) (testBit cs 0) in
        rewrite eq in orSo (Right nbr)
  in Evidence (ih .fst) (Drop (rewrite shiftRAnd bs cs 1 in ih .snd) x)
meet (Drop thl x @{nbl}) (Keep thr x) =
  let ih = meet thl thr in
  let 0 nb : So (not $ testBit (bs .&. cs) 0)
      = rewrite testBitAnd bs cs 0 in
        let eq = notAndIsOr (testBit bs 0) (testBit cs 0) in
        rewrite eq in orSo (Left nbl)
  in Evidence (ih .fst) (Drop (rewrite shiftRAnd bs cs 1 in ih .snd) x)
meet (Drop thl x @{nbl}) (Drop thr x) =
  let ih = meet thl thr in
  let 0 nb : So (not $ testBit (bs .&. cs) 0)
      = rewrite testBitAnd bs cs 0 in
        let eq = notAndIsOr (testBit bs 0) (testBit cs 0) in
        rewrite eq in orSo (Left nbl)
  in Evidence (ih .fst) (Drop (rewrite shiftRAnd bs cs 1 in ih .snd) x)

-- We need to public export so that `fst (join th ph)` computes at the type level.
-- These are all runtime irrelevant though so their behaviour does not matter.
public export
join : Thinning i bs sxl sx -> Thinning i cs sxr sx ->
       Exists $ \ sxlr => Thinning i (bs .|. cs) sxlr sx
join Done Done = Evidence ? Done
join (Keep thl x @{bl}) (Keep thr x) =
  let ih = join thl thr in
  let 0 b : So (testBit (bs .|. cs) 0)
      = rewrite testBitOr bs cs 0 in
        orSo (Left bl)
  in Evidence (ih .fst :< x) (Keep (rewrite shiftROr bs cs 1 in ih .snd) x)
join (Keep thl x @{bl}) (Drop thr x) =
  let ih = join thl thr in
  let 0 b : So (testBit (bs .|. cs) 0)
      = rewrite testBitOr bs cs 0 in
        orSo (Left bl)
  in Evidence (ih .fst :< x) (Keep (rewrite shiftROr bs cs 1 in ih .snd) x)
join (Drop thl x) (Keep thr x @{br}) =
  let ih = join thl thr in
  let 0 b : So (testBit (bs .|. cs) 0)
      = rewrite testBitOr bs cs 0 in
        orSo (Right br)
  in Evidence (ih .fst :< x) (Keep (rewrite shiftROr bs cs 1 in ih .snd) x)
join (Drop thl x @{nbl}) (Drop thr x @{nbr}) =
  let ih = join thl thr in
  let 0 b : So (not $ testBit (bs .|. cs) 0)
      = rewrite testBitOr bs cs 0 in
        let eq = notOrIsAnd (testBit bs 0) (testBit cs 0) in
        rewrite eq in andSo (nbl, nbr)
  in Evidence (ih .fst) (Drop (rewrite shiftROr bs cs 1 in ih .snd) x)

------------------------------------------------------------------------------
-- Inversion principles
-- Simple observations about the Nat/Integer indices of a Thinning are enough
-- to guarantee a proof was built using a specific constructor.
------------------------------------------------------------------------------

||| Characterising Done-headed thinnings
public export
record IsDone {a : Type} {bs : Integer} {sx, sy : SnocList a} (th : Thinning 0 bs sx sy) where
  constructor MkIsDone
  bsIsZero       : bs === 0
  fstIndexIsLin  : sx === [<]
  sndIndexIsLin  : sy === [<]
  thinningIsDone : (th ===)
                 $ replace {p = \ bs => Thinning 0 bs sx sy} (sym bsIsZero)
                 $ replace {p = Thinning 0 0 sx} (sym sndIndexIsLin)
                 $ replace {p = flip (Thinning 0 0) [<]} (sym fstIndexIsLin)
                 $ Done

||| Proof that whenever the big end is 0, the thinning is Done
export
isDone : (th : Thinning 0 bs sx sy) -> IsDone th
isDone Done = MkIsDone Refl Refl Refl Refl

||| Characterising Keep-headed thinnings
public export
record IsKeep
  {a : Type} {i : Nat} {bs : Integer} {sx, sy : SnocList a}
  (th : Thinning (S i) bs sx sy)
  (b : So (testBit bs Z)) where
  constructor MkIsKeep
  {0 fstIndexTail, sndIndexTail, keptHead : _}
  fstIndexIsSnoc : sx === fstIndexTail :< keptHead
  sndIndexIsSnoc : sy === sndIndexTail :< keptHead
  subThinning    : Thinning i (bs `shiftR` 1) fstIndexTail sndIndexTail
  thinningIsKeep : (th ===)
     $ replace {p = Thinning (S i) bs sx} (sym sndIndexIsSnoc)
     $ replace {p = flip (Thinning (S i) bs) (sndIndexTail :< keptHead)} (sym fstIndexIsSnoc)
     $ Keep subThinning keptHead

export
isKeepInteger : (bs : Integer) -> So (testBit bs Z) -> bs === setBit ((bs `shiftR` 1) `shiftL` 1) 0
isKeepInteger bs so = sym $ extensionally $ \case
  Z => transitive (soToEq $ testSetBitSame ((bs `shiftR` 1) `shiftL` 1) Z) (sym $ soToEq so)
  S i => transitive (testSetBitOther ((bs `shiftR` 1) `shiftL` 1) Z (S i) absurd)
       $ transitive (testBitSShiftL (bs `shiftR` 1) 0 i)
       $ transitive (cong (`testBit` i) (shiftL0 (bs `shiftR` 1)))
       $ testBitShiftR bs 1 i

||| Proof that whenever the big end is (S i), and the (S i)-bit is set
||| then the thinning is Keep-headed
public export
isKeep : (th : Thinning (S i) bs sx sy) -> (b : So (testBit bs Z)) -> IsKeep th b
isKeep (Drop th x {nb}) b = void (soNotToNotSo nb b)
isKeep (Keep th x {b = b1}) b2
  = MkIsKeep Refl Refl th (cong (\ b => Keep th x {b}) (irrelevantSo b1 b2))


||| Characterising Drop-headed thinnings
public export
record IsDrop
  {a : Type} {i : Nat} {bs : Integer} {sx, sy : SnocList a}
  (th : Thinning (S i) bs sx sy)
  (b : So (not $ testBit bs Z)) where
  constructor MkIsDrop
  {0 sndIndexTail, keptHead : _}
  sndIndexIsSnoc : sy === sndIndexTail :< keptHead
  subThinning    : Thinning i (bs `shiftR` 1) sx sndIndexTail
  thinningIsDrop : (th ===)
     $ replace {p = Thinning (S i) bs sx} (sym sndIndexIsSnoc)
     $ Drop subThinning keptHead

||| Proof that whenever the big end is (S i), and the (S i)-bit is not set
||| then the thinning is Drop-headed
public export
isDrop : (th : Thinning (S i) bs sx sy) -> (nb : So (not $ testBit bs Z)) -> IsDrop th nb
isDrop (Keep th x {b}) nb = void (soNotToNotSo nb b)
isDrop (Drop th x {nb = nb1}) nb2 = MkIsDrop Refl th (cong (\ nb => Drop th x {nb}) (irrelevantSo nb1 nb2))


export
isDropInteger : (bs : Integer) -> So (not $ testBit bs Z) -> bs === (bs `shiftR` 1) `shiftL` 1
isDropInteger bs so = sym $ extensionally $ \case
  Z => transitive (testBit0ShiftL (bs `shiftR` 1) 0)
     $ transitive (sym $ cong not $ soToEq so)
     $ notInvolutive (testBit bs Z)
  S i => transitive (testBitSShiftL (bs `shiftR` 1) 0 i)
       $ transitive (cong (`testBit` i) (shiftL0 (bs `shiftR` 1)))
       $ testBitShiftR bs 1 i

export
bit : {sx : SnocList a} -> AtIndex i x sx -> Thinning (length sx) (bit i) [<x] sx
bit Z = Keep (none ?) x
bit (S p) =
  let 0 nb : So (not $ testBit (the Integer $ bit i) 0)
           = eqToSo $ cong not $ testBit0ShiftL 1 (pred i) in
  Drop (rewrite shiftRBitS (pred i) in bit p) ?

export
(++) : Thinning i bs sa sb -> Thinning j cs sx sy ->
       Thinning (i + j) (cs .|. (bs `shiftL` j)) (sa ++ sx) (sb ++ sy)
th ++ Done
  = rewrite plusZeroRightNeutral i in
    rewrite shiftL0 bs in
    rewrite orZeroBitsLeftIdentity bs in
    th
th ++ Keep {i = j} ph x @{so}
  = rewrite sym $ plusSuccRightSucc i j in
    Keep
    (rewrite shiftROr cs (bs `shiftL` S j) 1 in
     rewrite shiftLSR bs j in
     th ++ ph)
    x
    @{rewrite testBitOr cs (bs `shiftL` S j) 0 in
      rewrite testBit0ShiftL bs j in
      rewrite orFalseNeutral (testBit {a = Integer} cs Z) in
      so}
th ++ Drop {i = j} ph x @{soNot}
  = rewrite sym $ plusSuccRightSucc i j in
    Drop
    (rewrite shiftROr cs (bs `shiftL` S j) 1 in
     rewrite shiftLSR bs j in
     th ++ ph)
    x
    @{rewrite testBitOr cs (bs `shiftL` S j) 0 in
      rewrite testBit0ShiftL bs j in
      rewrite orFalseNeutral (testBit {a = Integer} cs Z) in
      soNot}
