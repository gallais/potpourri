module Thin

import Data.Bits
import Data.Bits.Integer
import Data.DPair
import Data.SnocList

import Thin.Internal

%default total

------------------------------------------------------------------------------
-- Type and interfaces
------------------------------------------------------------------------------

||| A Th is a thin wrapper around Thinning that only keeps the
||| minimal amount of information as runtime relevant.
public export
record Th {a : Type} (sx, sy : SnocList a) where
  constructor MkTh
  bigEnd     : Nat
  encoding   : Integer
  0 thinning : Thinning bigEnd encoding sx sy

infixr 5 *^
public export
interface Thable (0 t : SnocList a -> Type) where
  (*^) : {0 sa, sb : SnocList a} -> t sa -> Th sa sb -> t sb

infixr 5 ^?
public export
interface Selable (0 t : SnocList a -> Type) where
  (^?) : {0 sa, sb : SnocList a} -> Th sa sb -> t sb -> t sa

------------------------------------------------------------------------------
-- Smart constructors
------------------------------------------------------------------------------

export
done : Th [<] [<]
done = MkTh Z 0 Done

export
keep : Th sx sy -> (0 x : a) -> Th (sx :< x) (sy :< x)
keep th x
  = MkTh (S th .bigEnd) (setBit (th .encoding `shiftL` 1) Z)
  $ let 0 b = testSetBitSame (th .encoding `shiftL` 1) Z in
    Keep (rewrite setBit0shiftR (th .encoding `shiftL` 1) in
          rewrite shiftLR (th .encoding) in th.thinning) x

export
drop : Th sx sy -> (0 x : a) -> Th sx (sy :< x)
drop th x
  = MkTh (S th .bigEnd) (th .encoding `shiftL` 1)
  $ let 0 nb = eqToSo $ cong not $ testBit0ShiftL (th .encoding) 0 in
    Drop (rewrite shiftLR (th .encoding) in th .thinning) x

------------------------------------------------------------------------------
-- Smart destructor (aka view)
------------------------------------------------------------------------------

public export
data View : Th sx sy -> Type where
  VDone :                                 View Thin.done
  VKeep : (th : Th sx sy) -> (0 x : a) -> View (keep th x)
  VDrop : (th : Th sx sy) -> (0 x : a) -> View (drop th x)

cast : {0 th, th' : Thinning i bs sx sy} ->
       View (MkTh i bs th) ->
       View (MkTh i bs th')
cast v = replace {p = \ th => View (MkTh i bs th)} (irrelevantThinning ? ?) v

export %inline
view : (th : Th sx sy) -> View th
view (MkTh 0 bs th) =
  let 0 eqs = isDone th in
  rewrite bsIsZero eqs in
  rewrite fstIndexIsLin eqs in
  rewrite sndIndexIsLin eqs in
  rewrite thinningIsDone eqs in
  VDone
view (MkTh (S i) bs th) = case choose (testBit bs Z) of
  Left so =>
    let 0 eqs = isKeep th so in
    rewrite fstIndexIsSnoc eqs in
    rewrite sndIndexIsSnoc eqs in
    rewrite thinningIsKeep eqs in
    rewrite isKeepInteger bs so in
    cast $ VKeep (MkTh i (bs `shiftR` 1) eqs.subThinning) eqs.keptHead
  Right soNot =>
    let 0 eqs = isDrop th soNot in
    rewrite sndIndexIsSnoc eqs in
    rewrite thinningIsDrop eqs in
    rewrite isDropInteger bs soNot in
    cast $ VDrop (MkTh i (bs `shiftR` 1) eqs.subThinning) eqs.keptHead

------------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------------

export
Thable (Th sx) where
  th *^ ph = case view ph of
    VDone => th
    VDrop ph x => drop (th *^ ph) x
    VKeep ph x => case view th of
      VKeep th x => keep (th *^ ph) x
      VDrop th x => drop (th *^ ph) x

export
Selable (`Th` sy) where
  (^?) = (*^)

export
Show (Th sx sy) where
  show th = pack ('[' :: go th [']']) where
    go : Th sa sb -> List Char -> List Char
    go th = case view th of
      VDone => id
      VKeep th x => go th . ('1'::)
      VDrop th x => go th . ('0'::)

------------------------------------------------------------------------------
-- Combinators
------------------------------------------------------------------------------

||| Empty thinning
-- TODO: only take the length as an argument?
export
none : (sx : SnocList a) -> Th [<] sx
none sx = MkTh (length sx) zeroBits (none sx)

{-
||| Identity thinning
-- TODO: only take the length as an argument?
export
ones : (sx : SnocList a) -> Th sx sx
ones sx = MkTh (length sx) oneBits (ones sx)
-}

export
meet : Th sxl sx -> Th sxr sx -> Exists (`Th` sx)
meet thl thr
  = Evidence ?
  $ MkTh (thl .bigEnd) (thl .encoding .&. thr .encoding)
  $ snd $ Internal.meet (thl .thinning)
  $ rewrite irrelevantSize (thl .thinning) (thr .thinning) in thr .thinning

export
isMeet : (th : Th sxl sx) -> (ph : Th sxr sx) ->
         (Th (fst $ meet th ph) sxl, Th (fst $ meet th ph) sxr)
isMeet th ph = case view th of
  VDone => case view ph of
    VDone => (done, done)
  VKeep th x => case view ph of
    VKeep ph x => bimap (`keep` x) (`keep` x) (isMeet th ph)
    VDrop ph x => mapFst (`drop` x) (isMeet th ph)
  VDrop th x => case view ph of
    VKeep ph x => mapSnd (`drop` x) (isMeet th ph)
    VDrop ph x => isMeet th ph

export
join : Th sxl sx -> Th sxr sx -> Exists (`Th` sx)
join thl thr
  = Evidence ?
  $ MkTh (thl .bigEnd) (thl .encoding .|. thr .encoding)
  $ snd $ Internal.join (thl .thinning)
  $ rewrite irrelevantSize (thl .thinning) (thr .thinning) in thr .thinning

||| Concatenate two thinnings
export
(++) : Th sa sb -> Th sx sy -> Th (sa ++ sx) (sb ++ sy)
thl ++ thr = case view thr of
  VDone => thl
  VKeep thr x => keep (thl ++ thr) x
  VDrop thr x => drop (thl ++ thr) x

||| Like filter but returns a thinning
export
which : (a -> Bool) -> (sy : SnocList a) -> (sx : SnocList a ** Th sx sy)
which p [<] = ([<] ** done)
which p (sy :< y)
  = ifThenElse (p y)
     (bimap (:< y) (`keep` y))
     (bimap id (`drop` y))
     (which p sy)

{-
test : List (sx : SnocList Nat ** Th sx ([<] <>< [0..10]))
test = flip map [2..5] $ \ i =>
        which (\ n => n `mod` i /= 0) ([<] <>< [0..10])
-}
