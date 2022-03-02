module Thin

import Data.Bits
import Data.Bits.Integer
import Data.SnocList

import Thin.Internal

%default total

------------------------------------------------------------------------------
-- Type and interfaces
------------------------------------------------------------------------------

||| A Th is a thin wrapper around Thinning that only keeps the
||| minimal amount of information as runtime relevant.
record Th {a : Type} (sx, sy : SnocList a) where
  constructor MkTh
  bigEnd     : Nat
  encoding   : Integer
  0 thinning : Thinning bigEnd encoding sx sy

infixr 5 *^
interface Thable (0 t : SnocList a -> Type) where
  (*^) : {0 sa, sb : SnocList a} -> t sa -> Th sa sb -> t sb

infixr 5 ^?
interface Selable (0 t : SnocList a -> Type) where
  (^?) : {0 sa, sb : SnocList a} -> Th sa sb -> t sb -> t sa

------------------------------------------------------------------------------
-- Smart constructors
------------------------------------------------------------------------------

export
done : (i : Integer) -> Th [<] [<]
done i = MkTh Z i Done

export
keep : Th sx sy -> (0 x : a) -> Th (sx :< x) (sy :< x)
keep (MkTh i bs th) x
  = MkTh (S i) (setBit bs (S i))
  $ let 0 b = testSetBitSame (S i) bs in
    Keep (setBitPreserve {j = S i} th reflexive) x

export
drop : Th sx sy -> (0 x : a) -> Th sx (sy :< x)
drop (MkTh i bs th) x
  = MkTh (S i) (clearBit bs (S i))
  $ let 0 nb = testClearBitSame (S i) bs in
    Drop (clearBitPreserve {j = S i} th reflexive) x

------------------------------------------------------------------------------
-- Smart destructor (aka view)
------------------------------------------------------------------------------

public export
data View : Th sx sy -> Type where
  VDone : (i : Integer)   -> View (done i)
  VKeep : (th : Th sx sy) -> (0 x : a) -> {auto 0 b : So ?} ->
          View (MkTh (S th.bigEnd) th.encoding (Keep th.thinning x {b}))
  VDrop : (th : Th sx sy) -> (0 x : a) -> {auto 0 nb : So (not ?)} ->
          View (MkTh (S th.bigEnd) th.encoding (Drop th.thinning x {nb}))

export
view : (th : Th sx sy) -> View th
view (MkTh 0 i th) =
  let 0 eqs = isDone th in
  rewrite fstIndexIsLin eqs in
  rewrite sndIndexIsLin eqs in
  rewrite thinningIsDone eqs in
  VDone i
view (MkTh (S n) i th) = case choose (testBit i (S n)) of
  Left so =>
    let 0 eqs = isKeep th so in
    rewrite fstIndexIsSnoc eqs in
    rewrite sndIndexIsSnoc eqs in
    rewrite thinningIsKeep eqs in
    VKeep (MkTh n i (subThinning eqs)) ?
  Right soNot =>
    let 0 eqs = isDrop th soNot in
    rewrite sndIndexIsSnoc eqs in
    rewrite thinningIsDrop eqs in
    VDrop (MkTh n i (subThinning eqs)) ?

------------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------------

export
Thable (Th sx) where
  th *^ ph = case view ph of
    VDone i => th
    VDrop ph x => drop (th *^ ph) x
    VKeep ph x => case view th of
      VKeep th x => keep (th *^ ph) x
      VDrop th x => drop (th *^ ph) x

export
Selable (`Th` sy) where
  (^?) = (*^)

Show (Th sx sy) where
  show th = pack ('[' :: go th [']']) where
    go : Th sa sb -> List Char -> List Char
    go th = case view th of
      VDone _ => id
      VKeep th x => go th . ('1'::)
      VDrop th x => go th . ('0'::)

------------------------------------------------------------------------------
-- Combinators
------------------------------------------------------------------------------

none : (sx : SnocList a) -> Th [<] sx
none [<] = done 0
none (sx :< x) = drop (none sx) x

ones : (sx : SnocList a) -> Th sx sx
ones [<] = done 0
ones (sx :< x) = keep (ones sx) x

(++) : Th sa sb -> Th sx sy -> Th (sa ++ sx) (sb ++ sy)
thl ++ thr = case view thr of
  (VDone _) => thl
  (VKeep thr x) => keep (thl ++ thr) x
  (VDrop thr x) => drop (thl ++ thr) x
