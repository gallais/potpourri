module Thin

import Data.Bool.Decidable
import Data.Bits
import Data.Bits.Integer
import Data.DPair
import Data.SnocList
import Decidable.Equality

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
  = MkTh (S th .bigEnd) (cons True (th .encoding))
  $ let 0 b = eqToSo $ testBit0Cons True (th .encoding) in
    Keep (rewrite consShiftR True (th .encoding) in th.thinning) x

export
drop : Th sx sy -> (0 x : a) -> Th sx (sy :< x)
drop th x
  = MkTh (S th .bigEnd) (cons False (th .encoding))
  $ let 0 nb = eqToSo $ cong not $ testBit0Cons False (th .encoding) in
    Drop (rewrite consShiftR False (th .encoding) in th .thinning) x

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
-- Unfold lemmas for the view
------------------------------------------------------------------------------

chooseTrueUnfold : choose True === Left Oh
chooseTrueUnfold with (choose True)
  _ | Left Oh = Refl
  _ | Right ohno = absurd ohno

chooseFalseUnfold : choose False === Right Oh
chooseFalseUnfold with (choose False)
  _ | Left ohyes = absurd ohyes
  _ | Right Oh = Refl

export
viewDoneUnfold : view Thin.done === VDone
viewDoneUnfold = Refl

export
viewKeepUnfold : (th : Th sx sy) -> view (keep th x) === VKeep th x
viewKeepUnfold (MkTh i bs p)
  = rewrite testBit0Cons True bs in
    rewrite chooseTrueUnfold in
    rewrite consShiftR True bs in
    Refl

export
viewDropUnfold : (th : Th sx sy) -> view (drop th x) === VDrop th x
viewDropUnfold (MkTh i bs p)
  = rewrite testBit0Cons False bs in
    rewrite chooseFalseUnfold in
    rewrite consShiftR False bs in
    Refl

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

||| This definition makes the proofs easier.
||| If we proceed by `case (view th) of ...` instead, things get horrible
export
eqView : {th, ph : Th sa sb} -> View th -> View ph -> Bool
eqView VDone _ = True
eqView (VKeep th _) (VKeep ph _) = eqView (view th) (view ph)
eqView (VDrop th _) (VDrop ph _) = eqView (view th) (view ph)
eqView _ _ = False

export
Eq (Th sx sy) where
  th == ph = eqView (view th) (view ph)

export
Show (Th sx sy) where
  show th = pack ('[' :: go th [']']) where
    go : Th sa sb -> List Char -> List Char
    go th = case view th of
      VDone => id
      VKeep th x => go th . ('1'::)
      VDrop th x => go th . ('0'::)

------------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------------

export
keepInjective : (th, ph : Th sx sy) -> keep th x === keep ph x -> th === ph
keepInjective (MkTh i bs p) (MkTh j cs q) eq
  with (cong (pred . bigEnd) eq)
  keepInjective (MkTh i bs p) (MkTh i cs q) eq | Refl
    with (consInjective True bs cs (cong encoding eq))
    keepInjective (MkTh i bs p) (MkTh i bs q) eq | Refl | Refl
      = rewrite irrelevantThinning p q in Refl

export
dropInjective : (th, ph : Th sx sy) -> drop th x === drop ph x -> th === ph
dropInjective (MkTh i bs p) (MkTh j cs q) eq
  with (cong (pred . bigEnd) eq)
  dropInjective (MkTh i bs p) (MkTh i cs q) eq | Refl
    with (shiftLInjective bs cs 1 (cong encoding eq))
    dropInjective (MkTh i bs p) (MkTh i bs q) eq | Refl | Refl
      = rewrite irrelevantThinning p q in Refl

export
eqViewReflects : {th, ph : Th sx sy} -> (v : View th) -> (w : View ph) ->
                 Reflects (th === ph) (eqView v w)
eqViewReflects VDone VDone = RTrue Refl
eqViewReflects (VKeep th x) (VKeep ph x)
  -- shuffling things around so that abstraction happens in the right order
  with (eqViewReflects (view th) (view ph))
  _ | p with (eqView (view th) (view ph))
    _ | b = case p of
      RTrue eq => RTrue (cong (`keep` x) eq)
      RFalse neq => RFalse (neq . keepInjective th ph)
eqViewReflects (VKeep th x) (VDrop ph x) = RFalse (\case hyp impossible)
eqViewReflects (VDrop th x) (VKeep ph x) = RFalse (\case hyp impossible)
eqViewReflects (VDrop th x) (VDrop ph x) with (eqViewReflects (view th) (view ph))
  _ | p with (eqView (view th) (view ph))
    _ | b = case p of
      RTrue eq => RTrue (cong (`drop` x) eq)
      RFalse neq => RFalse (neq . dropInjective th ph)

||| Boolean equality on thinnings reflects propositional equality.
export
eqReflects : (th, ph : Th {a} sx sy) -> Reflects (th === ph) (th == ph)
eqReflects th ph = eqViewReflects (view th) (view ph)

||| If we know there's a boolean that reflects a type then the type is decidable

export
toDec : Reflects p b -> Dec p
toDec (RTrue yes) = Yes yes
toDec (RFalse no) = No no

||| As a consequence equality of thinnings is decidable
export
DecEq (Th sx sy) where
  decEq th ph = toDec (eqReflects th ph)

------------------------------------------------------------------------------
-- Empty and identity thinnings
------------------------------------------------------------------------------

||| Empty thinning
-- TODO: only take the length as an argument?
export
none : (sx : SnocList a) -> Th [<] sx
none sx = MkTh (length sx) zeroBits (none sx)

||| Identity thinning
-- TODO: only take the length as an argument?
export
ones : (sx : SnocList a) -> Th sx sx
ones sx = let i : Nat; i = length sx in MkTh i (full i) (ones sx)

------------------------------------------------------------------------------
-- And their properties

export
tooBig : {sx : SnocList a} -> Not (Th (sx :< x) sx)
tooBig th = case view th of
  VKeep th x => tooBig th
  VDrop th x => tooBig (drop (ones ?) ? *^ th)

export
irrelevantDone : (th : Th [<] [<]) -> th === Thin.done
irrelevantDone th = case view th of VDone => Refl

export
irrelevantNone : (th, ph : Th [<] sx) -> th === ph
irrelevantNone th ph = case view th of
  VDone => sym $ irrelevantDone ph
  VDrop th x => case view ph of
    VDrop ph x => cong (`drop` x) (irrelevantNone th ph)

export
noneIsDrop : none (sx :< x) === drop (none sx) x
noneIsDrop = irrelevantEq $ irrelevantNone ? ?

export
irrelevantOnes : (th, ph : Th sx sx) -> th === ph
irrelevantOnes th ph = case view th of
  VDone => sym $ irrelevantDone ph
  VKeep th x => case view ph of
    VKeep ph x => cong (`keep` x) (irrelevantOnes th ph)
    VDrop ph x => void $ tooBig ph
  VDrop th x => void $ tooBig th

export
onesIsKeep : ones (sx :< x) === keep (ones sx) x
onesIsKeep = irrelevantEq $ irrelevantOnes ? ?

------------------------------------------------------------------------------
-- Intersection & union of supports
------------------------------------------------------------------------------

export
meet : Th sxl sx -> Th sxr sx -> Exists (`Th` sx)
meet thl thr
  = Evidence ?
  $ MkTh (thl .bigEnd) (thl .encoding .&. thr .encoding)
  $ snd $ Internal.meet (thl .thinning)
  $ rewrite irrelevantSize (thl .thinning) (thr .thinning) in thr .thinning

||| Meet is indeed computing a lower bound
||| TODO: prove it is the largest such
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

||| Join is indeed computing an upper bound
||| TODO: prove it is the smallest such
export
isJoin : (th : Th sxl sx) -> (ph : Th sxr sx) ->
         (Th sxl (fst $ join th ph), Th sxr (fst $ join th ph))
isJoin th ph = case view th of
  VDone => case view ph of
    VDone => (done, done)
  VKeep th x => case view ph of
    VKeep ph x => bimap (`keep` x) (`keep` x) (isJoin th ph)
    VDrop ph x => bimap (`keep` x) (`drop` x) (isJoin th ph)
  VDrop th x => case view ph of
    VKeep ph x => bimap (`drop` x) (`keep` x) (isJoin th ph)
    VDrop ph x => isJoin th ph

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
