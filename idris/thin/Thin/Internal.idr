||| This is the low-level stuff used to implement Thin.
||| The even lower level (sometimes unsafe) results are in Data.Bits.Integer

module Thin.Internal

import Data.Bool
import Data.Bits
import Data.Bits.Integer
import Data.DPair
import Data.Nat
import Data.SnocList

%default total

------------------------------------------------------------------------------
-- TODO: move to stdlib
------------------------------------------------------------------------------

ltNotEq : {m, n : Nat} -> m `LT` n -> Not (m === n)
ltNotEq lt = case view lt of
  LTZero => absurd
  LTSucc lt => ltNotEq lt . cong pred

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
  Done : Thinning Z bs [<] [<]
  ||| If the last bit of interest is set then the snoclist's head is kept
  Keep : Thinning i bs sx sy -> (0 x : a) ->
         {auto 0 b  : So (      testBit bs (S i))} ->
         Thinning (S i) bs (sx :< x) (sy :< x)
  ||| If the last bit of interest is not set then the snoclist's head is thrown out
  Drop : Thinning i bs sx sy -> (0 x : a) ->
         {auto 0 nb : So (not $ testBit bs (S i))} ->
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

||| If we set a bit beyond the segment of interest, the thinning is unaffected
export
setBitPreserve : Thinning i bs sx sy -> (0 _ : i `LT` j) -> Thinning i (setBit bs j) sx sy
setBitPreserve Done lt = Done
setBitPreserve (Keep th x {b}) lt =
  let 0 eq = testSetBitOther j i (\ eq => ltNotEq lt (sym eq)) bs in
  let 0 lt = transitive (lteSuccRight reflexive) lt in
  let 0 b = replace {p = So} (sym eq) b in
  Keep (setBitPreserve th lt) x
setBitPreserve (Drop th x {nb}) lt =
  let 0 eq = testSetBitOther j i (\ eq => ltNotEq lt (sym eq)) bs in
  let 0 lt = transitive (lteSuccRight reflexive) lt in
  let 0 nb = replace {p = So . not} (sym eq) nb in
  Drop (setBitPreserve th lt) x

||| If we clear a bit beyond the segment of interest, the thinning is unaffected
export
clearBitPreserve : Thinning i bs sx sy -> (0 _ : i `LT` j) -> Thinning i (clearBit bs j) sx sy
clearBitPreserve Done lt = Done
clearBitPreserve (Keep th x {b}) lt =
  let 0 eq = testClearBitOther j i (\ eq => ltNotEq lt (sym eq)) bs in
  let 0 lt = transitive (lteSuccRight reflexive) lt in
  let 0 b = replace {p = So} (sym eq) b in
  Keep (clearBitPreserve th lt) x
clearBitPreserve (Drop th x {nb}) lt =
  let 0 eq = testClearBitOther j i (\ eq => ltNotEq lt (sym eq)) bs in
  let 0 lt = transitive (lteSuccRight reflexive) lt in
  let 0 nb = replace {p = So . not} (sym eq) nb in
  Drop (clearBitPreserve th lt) x

export
none : (sy : SnocList a) -> Thinning (length sy) Bits.zeroBits [<] sy
none [<] = Done
none (sy :< y) =
  let 0 nb = eqToSo (cong not $ testBitZeroBits (S $ length sy)) in
  Drop (none sy) y

export
ones : (sx : SnocList a) -> Thinning (length sx) Bits.oneBits sx sx
ones [<] = Done
ones (sx :< x) =
  let 0 nb = eqToSo (testBitOneBits (S $ length sx)) in
  Keep (ones sx) x

export
meet : Thinning i bs sxl sx -> Thinning i cs sxr sx ->
       Exists $ \ sxlr => Thinning i (bs .&. cs) sxlr sx
meet Done Done = Evidence [<] Done
meet {i = S i} (Keep thl x @{bl}) (Keep thr x @{br}) =
  let Evidence sxlr thm = meet thl thr in
  let 0 b : So (testBit (bs .&. cs) (S i))
      = rewrite testBitAnd (S i) bs cs in
        andSo (bl, br)
  in Evidence (sxlr :< x) (Keep thm x)
meet {i = S i} (Keep thl x) (Drop thr x @{nbr}) =
  let Evidence sxlr thm = meet thl thr in
  let 0 nb : So (not $ testBit (bs .&. cs) (S i))
      = rewrite testBitAnd (S i) bs cs in
        rewrite notAndIsOr (testBit bs (S i)) (testBit cs (S i)) in
        orSo (Right nbr)
  in Evidence sxlr (Drop thm x)
meet {i = S i} (Drop thl x @{nbl}) (Keep thr x) =
  let Evidence sxlr thm = meet thl thr in
  let 0 nb : So (not $ testBit (bs .&. cs) (S i))
      = rewrite testBitAnd (S i) bs cs in
        rewrite notAndIsOr (testBit bs (S i)) (testBit cs (S i)) in
        orSo (Left nbl)
  in Evidence sxlr (Drop thm x)
meet {i = S i} (Drop thl x @{nbl}) (Drop thr x) =
  let Evidence sxlr thm = meet thl thr in
  let 0 nb : So (not $ testBit (bs .&. cs) (S i))
      = rewrite testBitAnd (S i) bs cs in
        rewrite notAndIsOr (testBit bs (S i)) (testBit cs (S i)) in
        orSo (Left nbl)
  in Evidence sxlr (Drop thm x)

export
join : Thinning i bs sxl sx -> Thinning i cs sxr sx ->
       Exists $ \ sxlr => Thinning i (bs .|. cs) sxlr sx
join Done Done = Evidence [<] Done
join {i = S i} (Keep thl x @{bl}) (Keep thr x) =
  let Evidence sxlr thm = join thl thr in
  let 0 b : So (testBit (bs .|. cs) (S i))
      = rewrite testBitOr (S i) bs cs in
        orSo (Left bl)
  in Evidence (sxlr :< x) (Keep thm x)
join {i = S i} (Keep thl x @{bl}) (Drop thr x) =
  let Evidence sxlr thm = join thl thr in
  let 0 b : So (testBit (bs .|. cs) (S i))
      = rewrite testBitOr (S i) bs cs in
        orSo (Left bl)
  in Evidence (sxlr :< x) (Keep thm x)
join {i = S i} (Drop thl x) (Keep thr x @{br}) =
  let Evidence sxlr thm = join thl thr in
  let 0 b : So (testBit (bs .|. cs) (S i))
      = rewrite testBitOr (S i) bs cs in
        orSo (Right br)
  in Evidence (sxlr :< x) (Keep thm x)
join {i = S i} (Drop thl x @{nbl}) (Drop thr x @{nbr}) =
  let Evidence sxlr thm = join thl thr in
  let 0 b : So (not $ testBit (bs .|. cs) (S i))
      = rewrite testBitOr (S i) bs cs in
        rewrite notOrIsAnd (testBit bs (S i)) (testBit cs (S i)) in
        andSo (nbl, nbr)
  in Evidence sxlr (Drop thm x)

------------------------------------------------------------------------------
-- Inversion principles
-- Simple observations about the Nat/Integer indices of a Thinning are enough
-- to guarantee a proof was built using a specific constructor.
------------------------------------------------------------------------------

||| Characterising Done-headed thinnings
public export
record IsDone {a : Type} {bs : Integer} {sx, sy : SnocList a} (th : Thinning 0 bs sx sy) where
  constructor MkIsDone
  fstIndexIsLin  : sx === [<]
  sndIndexIsLin  : sy === [<]
  thinningIsDone : (th ===)
                 $ replace {p = Thinning 0 bs sx} (sym sndIndexIsLin)
                 $ replace {p = flip (Thinning 0 bs) [<]} (sym fstIndexIsLin)
                 $ Done

||| Proof that whenever the big end is 0, the thinning is Done
export
isDone : (th : Thinning 0 bs sx sy) -> IsDone th
isDone Done = MkIsDone Refl Refl Refl

||| Characterising Keep-headed thinnings
public export
record IsKeep
  {a : Type} {i : Nat} {bs : Integer} {sx, sy : SnocList a}
  (th : Thinning (S i) bs sx sy)
  (b : So (testBit bs (S i))) where
  constructor MkIsKeep
  {0 fstIndexTail, sndIndexTail, keptHead : _}
  fstIndexIsSnoc : sx === fstIndexTail :< keptHead
  sndIndexIsSnoc : sy === sndIndexTail :< keptHead
  subThinning    : Thinning i bs fstIndexTail sndIndexTail
  thinningIsKeep : (th ===)
                 $ replace {p = Thinning (S i) bs sx} (sym sndIndexIsSnoc)
                 $ replace {p = flip (Thinning (S i) bs) (sndIndexTail :< keptHead)} (sym fstIndexIsSnoc)
                 $ Keep subThinning keptHead

||| Proof that whenever the big end is (S i), and the (S i)-bit is set
||| then the thinning is Keep-headed
export
isKeep : (th : Thinning (S i) bs sx sy) -> (b : So (testBit bs (S i))) -> IsKeep th b
isKeep (Keep th x {b = b1}) b2 = MkIsKeep Refl Refl th (cong (\ b => Keep th x {b}) (irrelevantSo b1 b2))
isKeep (Drop th x {nb}) b = void (soNotToNotSo nb b)

||| Characterising Drop-headed thinnings
public export
record IsDrop
  {a : Type} {i : Nat} {bs : Integer} {sx, sy : SnocList a}
  (th : Thinning (S i) bs sx sy)
  (nb : So (not $ testBit bs (S i))) where
  constructor MkIsDrop
  {0 sndIndexTail, keptHead : _}
  sndIndexIsSnoc : sy === sndIndexTail :< keptHead
  subThinning    : Thinning i bs sx sndIndexTail
  thinningIsDrop : (th ===)
                 $ replace {p = Thinning (S i) bs sx} (sym sndIndexIsSnoc)
                 $ Drop subThinning keptHead

||| Proof that whenever the big end is (S i), and the (S i)-bit is clear
||| then the thinning is Drop-headed
export
isDrop : (th : Thinning (S i) bs sx sy) -> (nb : So (not $ testBit bs (S i))) -> IsDrop th nb
isDrop (Drop th x {nb = nb1}) nb2 = MkIsDrop Refl th (cong (\ nb => Drop th x {nb}) (irrelevantSo nb1 nb2))
isDrop (Keep th x {b}) nb = void (soNotToNotSo nb b)
