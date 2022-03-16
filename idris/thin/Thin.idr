module Thin

import Data.Bool.Decidable
import Data.Bits
import Data.Bits.Integer
import Data.DPair
import Data.SnocList
import Data.SnocList.Quantifiers
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

%name Th th, ph, ps

infixr 10 *^
public export
interface Thable (0 t : SnocList a -> Type) where
  (*^) : {0 sa, sb : SnocList a} -> t sa -> Th sa sb -> t sb

infixr 10 ^?
public export
interface Selable (0 t : SnocList a -> Type) where
  (^?) : {0 sa, sb : SnocList a} -> Th sa sb -> t sb -> t sa

------------------------------------------------------------------------------
-- Smart constructors
------------------------------------------------------------------------------

||| We define the smart constructors, deconstructors, combinators, etc. in a
||| nested namespace so that these definitions do not unfold in goals in the
||| main file. The eager unfolding made goals unreadable.
||| We will instead use the unfolding and irrelevance lemmas proved in the
||| nested namespace to step things when *we* need them to step.
namespace Smart

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
    VDone :                                 View Smart.done
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
  viewDoneUnfold : view Smart.done === VDone
  viewDoneUnfold = Refl

  export
  viewKeepUnfold : (th : Th sx sy) -> (0 x : a) -> view (keep th x) === VKeep th x
  viewKeepUnfold (MkTh i bs p) x
    = rewrite testBit0Cons True bs in
      rewrite chooseTrueUnfold in
      rewrite consShiftR True bs in
      Refl

  export
  viewDropUnfold : (th : Th sx sy) -> (0 x : a) -> view (drop th x) === VDrop th x
  viewDropUnfold (MkTh i bs p) x
    = rewrite testBit0Cons False bs in
      rewrite chooseFalseUnfold in
      rewrite consShiftR False bs in
      Refl

export
irrelevantDone : (th, ph : Th sx [<]) -> th === ph
irrelevantDone th ph = case view th of
  VDone => case view ph of
    VDone => Refl

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
Eq (Th sx sy) where
  th == ph = case view th of
    VDone => True
    VKeep th x => case view ph of
      VKeep ph x => th == ph
      VDrop ph x => False
    VDrop th x => case view ph of
      VKeep ph x => False
      VDrop ph x => th == ph

export
Show (Th sx sy) where
  show th = pack ('[' :: go th [']']) where
    go : Th sa sb -> List Char -> List Char
    go th = case view th of
      VDone => id
      VKeep th x => go th . ('1'::)
      VDrop th x => go th . ('0'::)

export
Thable (Any p) where
  psx *^ th = case view th of
    VDone => psx
    VKeep th x => case psx of
      Here px => Here px
      There psx => There (psx *^ th)
    VDrop th x => There (psx *^ th)

export
Selable (All p) where
  th ^? psy = case view th of
    VDone => [<]
    VKeep th x => let (psy :< py) = psy in th ^? psy :< py
    VDrop th x => let (psy :< py) = psy in th ^? psy

------------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------------

namespace Smart

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
  eqReflects : (th, ph : Th {a} sx sy) -> Reflects (th === ph) (th == ph)
  eqReflects {sx} {sy} th ph with (view th)
    eqReflects {sx = _} {sy = _} _ ph | VDone = RTrue (irrelevantDone ? ?)
    eqReflects {sx = _} {sy = _} _ ph | VKeep th x with (view ph)
      eqReflects {sx = _} {sy = _} _ _ | VKeep th x | VKeep ph x with (eqReflects th ph)
        _ | p with (th ==  ph)
          _ | b = case p of
            RTrue eq => RTrue (cong (`keep` x) eq)
            RFalse neq => RFalse (neq . keepInjective th ph)
      eqReflects {sx = _} {sy = _} _ _ | VKeep th x | VDrop ph x = RFalse (\case hyp impossible)
    eqReflects {sx = _} {sy = _} _ ph | VDrop th x with (view ph)
      eqReflects {sx = _} {sy = _} _ _ | VDrop th x | VKeep ph x = RFalse (\case hyp impossible)
      eqReflects {sx = _} {sy = _} _ _ | VDrop th x | VDrop ph x with (eqReflects th ph)
        _ | p with (th ==  ph)
          _ | b = case p of
            RTrue eq => RTrue (cong (`drop` x) eq)
            RFalse neq => RFalse (neq . dropInjective th ph)

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

namespace Smart

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
irrelevantNone : (th, ph : Th [<] sx) -> th === ph
irrelevantNone th ph = case view th of
  VDone => irrelevantDone ? ?
  VDrop th x => case view ph of
    VDrop ph x => cong (`drop` x) (irrelevantNone th ph)

export
noneIsDrop : none (sx :< x) === drop (none sx) x
noneIsDrop = irrelevantEq $ irrelevantNone ? ?

export
irrelevantOnes : (th, ph : Th sx sx) -> th === ph
irrelevantOnes th ph = case view th of
  VDone => irrelevantDone ? ?
  VKeep th x => case view ph of
    VKeep ph x => cong (`keep` x) (irrelevantOnes th ph)
    VDrop ph x => void $ tooBig ph
  VDrop th x => void $ tooBig th

export
onesIsKeep : (0 sx : SnocList a) -> (0 x : _) -> ones (sx :< x) === keep (ones sx) x
onesIsKeep sx x = irrelevantEq $ irrelevantOnes ? ?

export
onesLeftNeutral : (th : Th {a} sx sx) -> (ph : Th sx sy) -> th *^ ph === ph
onesLeftNeutral {sx} {sy} th ph with (view ph)
  onesLeftNeutral {sx = _} {sy = _} th _ | VDone = irrelevantDone ? ?
  onesLeftNeutral {sx = _} {sy = _} th _ | VKeep ph x with (view th)
    onesLeftNeutral {sx = _} {sy = _} _ _ | VKeep ph x | VKeep th x
      = cong (`keep` x) (onesLeftNeutral th ph)
    onesLeftNeutral {sx = _} {sy = _} _ _ | VKeep ph x | VDrop th x
      = void $ tooBig th
  onesLeftNeutral {sy = _} th _ | VDrop ph x = cong (`drop` x) (onesLeftNeutral th ph)

export
onesRightNeutral : (th : Th {a} sx sy) -> (ph : Th sy sy) -> th *^ ph === th
onesRightNeutral {sx} {sy} th ph with (view ph)
  onesRightNeutral {sy = _} th _ | VDone = Refl
  onesRightNeutral {sy = _} th _ | VKeep ph x with (view th)
    onesRightNeutral {sx = _} {sy = _} _ _ | VKeep ph x | VKeep th x
      = cong (`keep` x) (onesRightNeutral th ph)
    onesRightNeutral {sy = _} _ _ | VKeep ph x | VDrop th x
      = cong (`drop` x) (onesRightNeutral th ph)
  onesRightNeutral {sy = _} th _ | VDrop ph x = void $ tooBig ph

export
transAssoc : (th : Th {a} sw sx) -> (ph : Th sx sy) -> (ps : Th sy sz) ->
             ((th *^ ph) *^ ps) === (th *^ (ph *^ ps))
transAssoc {sw} {sx} {sy} {sz} th ph ps with (view ps)
  transAssoc {sy = _} {sz = _} th ph _ | VDone = irrelevantDone ? ?
  transAssoc {sy = _} {sz = _} th ph _ | VKeep ps x with (view ph)
    transAssoc {sx = _} {sy = _} {sz = _} th _ _ | VKeep ps x | VKeep ph x with (view th)
      transAssoc {sw = _} {sx = _} {sy = _} {sz = _} _ _ _ | VKeep ps x | VKeep ph x | VKeep th x
        = rewrite viewKeepUnfold (ph *^ ps) x in
          rewrite viewKeepUnfold (th *^ ph) x in
          rewrite viewKeepUnfold th x in
          cong (`keep` x) (transAssoc th ph ps)
      transAssoc {sw = _} {sx = _} {sy = _} {sz = _} _ _ _ | VKeep ps x | VKeep ph x | VDrop th x
        = rewrite viewKeepUnfold (ph *^ ps) x in
          rewrite viewDropUnfold (th *^ ph) x in
          rewrite viewDropUnfold th x in
          cong (`drop` x) (transAssoc th ph ps)
    transAssoc {sx = _} {sy = _} {sz = _} th _ _ | VKeep ps x | VDrop ph x
      = rewrite viewDropUnfold (ph *^ ps) x in
        rewrite viewDropUnfold (th *^ ph) x in
        cong (`drop` x) (transAssoc th ph ps)
  transAssoc {sz = _} th ph _ | VDrop ps x
    = rewrite viewDropUnfold (ph *^ ps) x in
      cong (`drop` x) (transAssoc th ph ps)

------------------------------------------------------------------------------
-- Intersection & union of supports
------------------------------------------------------------------------------

namespace Smart

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
