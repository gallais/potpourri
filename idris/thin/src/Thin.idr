module Thin

import Data.Bool.Decidable
import Data.Bool.Decidable.Extra
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

-- Snoclists are lists that grow on the right, just like contexts in typing
-- rules. They can be constructed using the empty snoclist constructor `Lin`
-- (sugared [<]) and `Snoc` (sugared (:<)).
-- They are defined in Idris 2's prelude.

||| A Th(inning) is a thin wrapper around Invariant that only keeps the
||| minimal amount of information as runtime relevant.
|||
||| A thinning from sx to sy is a proof that the snoclist sx can be
||| embedded in an order-preserving manner into sy.
|||
||| A less efficient but more common definition is:
|||
|||   data Th : (sx, sy : SnocList a) -> Type where
|||     Done : Th [<] [<]
|||     Keep : Th sx sy -> (0 x : a) -> Th (sx :< x) (sy :< x)
|||     Drop : Th sx sy -> (0 x : a) -> Th sx (sy :< x)
|||
public export
record Th {a : Type} (sx, sy : SnocList a) where
  constructor MkTh
  bigEnd : Nat
  encoding : Integer
  0 invariant : Invariant bigEnd encoding sx sy

%name Th th, ph, ps

infixr 10 *^
||| A type family t is Th(in)able if we can use a thinning from sa to sb
||| to transport values of type (t sa) to values of type (t sb).
public export
interface Thable (0 t : SnocList a -> Type) where
  (*^) : {0 sa, sb : SnocList a} -> t sa -> Th sa sb -> t sb

infixr 10 ^?
||| A type family t is Sel(ect)able if we can use a thinning from sa to sb
||| to restrict values of type (t sb) to values of type (t sa).
public export
interface Selable (0 t : SnocList a -> Type) where
  (^?) : {0 sa, sb : SnocList a} -> Th sa sb -> t sb -> t sa

------------------------------------------------------------------------------
-- Smart constructors
--
-- We can define smart constructors that allow us to build `Th` values
-- just as seamlessly as if we had defined it using the less efficient
-- formulation as an inductive family.
------------------------------------------------------------------------------

||| We define the smart constructors, deconstructors, combinators, etc. in a
||| nested namespace so that these definitions do not unfold in goals in the
||| main file. The eager unfolding made goals unreadable.
||| We will instead use the unfolding and irrelevance lemmas proved in the
||| nested namespace to step things when *we* need them to step.
namespace Smart

 export
 ||| The empty snoclist trivially embeds into itself
 done : Th [<] [<]
 done = MkTh { bigEnd = 0, encoding = 0, invariant = Done }

 export
 ||| Given an existing thinning th from sx to sy,
 ||| we can define a new one embedding (sx :< x) into (sy :< x)
 ||| that behaves like th on sx and simply propagates x
 keep : Th sx sy -> (0 x : a) -> Th (sx :< x) (sy :< x)
 keep th x = MkTh
  { bigEnd = S (th .bigEnd)
  , encoding = cons True (th .encoding)
  , invariant =
     let 0 b = eqToSo $ testBit0Cons True (th .encoding) in
     Keep (rewrite consShiftR True (th .encoding) in th.invariant) x
  }

 export
 ||| Given an existing thinning th from sx to sy,
 ||| we can define a new one embedding sx into (sy :< x)
 ||| that behaves like tx on sy and simply ignores x
 drop : Th sx sy -> (0 x : a) -> Th sx (sy :< x)
 drop th x = MkTh
  { bigEnd = S (th .bigEnd)
  , encoding = cons False (th .encoding)
  , invariant =
    let 0 prf = testBit0Cons False (th .encoding)
        0 nb = eqToSo $ cong not prf in
     Drop (rewrite consShiftR False (th .encoding) in th .invariant) x
 }

------------------------------------------------------------------------------
-- Smart destructor (aka view)
--
-- We can define a smart destructor that allows us to pattern match on Th
-- values just as seamlessly as if we had defined them using the less
-- efficient formulation as an inductive family
------------------------------------------------------------------------------

 ||| This sum type exposes three constructors corresponding to the three
 ||| smart constructors defined above.
 ||| By matching on a value of type (View th), we get to learn whether th
 ||| was built using done, keep, or drop.
 public export
 data View : Th sx sy -> Type where
   Done : View Smart.done
   Keep : (th : Th sx sy) -> (0 x : a) -> View (keep th x)
   Drop : (th : Th sx sy) -> (0 x : a) -> View (drop th x)

 ||| Auxiliary definition deploying the fact that the Invariant relation
 ||| is proof irrelevant
 cast : {0 th, th' : Invariant i bs sx sy} ->
        View (MkTh i bs th) ->
        View (MkTh i bs th')
 cast v = replace {p = \ th => View (MkTh i bs th)} (irrelevantInvariant ? ?) v

 ||| The view function proves that every Th value was necessarily built using
 ||| one of the three smart constructors.
 ||| This result empowers us to 'pattern-match' on Th values.
 export
 view : (th : Th sx sy) -> View th
 view (MkTh 0 bs prf) =
   let 0 eqs = isDone prf in
   rewrite bsIsZero eqs in
   rewrite fstIndexIsLin eqs in
   rewrite sndIndexIsLin eqs in
   rewrite invariantIsDone eqs in
   Done
 view (MkTh (S i) bs prf) = case choose (testBit bs Z) of
   Left so =>
     let 0 eqs = isKeep prf so in
     rewrite fstIndexIsSnoc eqs in
     rewrite sndIndexIsSnoc eqs in
     rewrite invariantIsKeep eqs in
     rewrite isKeepInteger bs so in
     let %inline th : Th eqs.fstIndexTail eqs.sndIndexTail
         th = MkTh i (bs `shiftR` 1) eqs.subInvariant in
     cast $ Keep th eqs.keptHead
   Right soNot =>
     let 0 eqs = isDrop prf soNot in
     rewrite sndIndexIsSnoc eqs in
     rewrite invariantIsDrop eqs in
     rewrite isDropInteger bs soNot in
     let %inline th : Th sx eqs.sndIndexTail
         th = MkTh i (bs `shiftR` 1) eqs.subInvariant in
     cast $ Drop th eqs.keptHead

 ||| Example of a use of `view`
 ||| @ sx is runtime irrelevant and yet we can compute its length because
 |||      it is precisely the number of Keep constructors (aka bits set to 1)
 |||      in the invariant that we have.
 kept : Th sx sy -> (n : Nat ** length sx === n)
 kept th = case view th of
   Done      => (0 ** Refl)
   Keep th x => let (n ** eq) = kept th in
                (S n ** cong S eq)
   Drop th x => kept th

------------------------------------------------------------------------------
-- Unfold lemmas for the view
------------------------------------------------------------------------------

 -- The inductive family So is defined in Idris 2's standard library module
 -- Data.So. It allows us to record whether a boolean holds.
 -- It is defined like so:
 --   data So : Bool -> Type where
 --     Oh : So True
 -- which means that a proof of type (So b) guarantees b is True.
 --
 -- The choose function also defined in Data.So states that every boolean is
 -- either True or its negation is. Its type is
 --   choose : (b : Bool) -> Either (So b) (So (not b))

 ||| Unfolding lemma for (choose True)
 chooseTrueUnfold : choose True === Left Oh
 chooseTrueUnfold with (choose True)
   _ | Left Oh = Refl
   _ | Right ohno = absurd ohno

 ||| Unfolding lemma for (choose False)
 chooseFalseUnfold : choose False === Right Oh
 chooseFalseUnfold with (choose False)
   _ | Left ohyes = absurd ohyes
   _ | Right Oh = Refl

 export
 ||| view correctly 'uncomputes' the smart constructor done
 viewDoneUnfold : view Smart.done === Done
 viewDoneUnfold = Refl

 export
 ||| view correctly 'uncomputes' the smart constructor keep
 viewKeepUnfold : (th : Th sx sy) -> (0 x : a) -> view (keep th x) === Keep th x
 viewKeepUnfold (MkTh i bs p) x
   = rewrite testBit0Cons True bs in
     rewrite chooseTrueUnfold in
     rewrite consShiftR True bs in
     Refl

 export
 ||| view correctly 'uncomputes' the smart constructor drop
 viewDropUnfold : (th : Th sx sy) -> (0 x : a) -> view (drop th x) === Drop th x
 viewDropUnfold (MkTh i bs p) x
   = rewrite testBit0Cons False bs in
     rewrite chooseFalseUnfold in
     rewrite consShiftR False bs in
     Refl

export
||| Thinnings into the empty snoclist are proof irrelevant
||| (because they cannot be anything but done, the empty thinning)
irrelevantDone : (th, ph : Th sx [<]) -> th === ph
irrelevantDone th ph = case view th of
  Done => case view ph of
    Done => Refl

------------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------------

||| Thinnings are thinnable (composition)
export
Thable (Th sx) where
  th *^ ph = case view ph of
    Done => th
    Drop ph x => drop (th *^ ph) x
    Keep ph x => case view th of
      Keep th x => keep (th *^ ph) x
      Drop th x => drop (th *^ ph) x

||| Thinnings are selectable (composition)
export
Selable (`Th` sy) where
  (^?) = (*^)

||| Equality can be checked cheaply by comparing the encodings
export
Eq (Th sx sy) where
  MkTh i bs _ == MkTh j cs _ = i == j && bs == cs

||| We can show thinnings as list of bits by taking them apart
||| constructor by constructor thanks to the view
export
Show (Th sx sy) where
  show th = pack ('[' :: go th [']']) where
    go : Th sa sb -> List Char -> List Char
    go th = case view th of
      Done => id
      Keep th x => go th . ('1'::)
      Drop th x => go th . ('0'::)

||| Given a thinning from sx to sy,
||| a proof that there is a value in sx that satisfies p can be
||| thinnned to a proof that there is a value in sy that satisfies p
export
Thable (Any p) where
  psx *^ th = case view th of
    Done => psx
    Keep th x => case psx of
      Here px => Here px
      There psx => There (psx *^ th)
    Drop th x => There (psx *^ th)

||| Given a thinning from sx to sy,
||| a proof that all of the values in sy satisfy p can be
||| selected to a proof that all the values in the sub-snoclist sx satisfy p
export
Selable (All p) where
  th ^? psy = case view th of
    Done => [<]
    Keep th x => let (psy :< py) = psy in th ^? psy :< py
    Drop th x => let (psy :< py) = psy in th ^? psy

------------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------------

namespace Smart

  ||| The keep smart constructor is injective
  export
  keepInjective : (th, ph : Th sx sy) -> keep th x === keep ph x -> th === ph
  keepInjective (MkTh i bs p) (MkTh j cs q) eq
    with (cong (pred . bigEnd) eq)
    keepInjective (MkTh i bs p) (MkTh i cs q) eq | Refl
      with (consInjective True bs cs (cong encoding eq))
      keepInjective (MkTh i bs p) (MkTh i bs q) eq | Refl | Refl
        = rewrite irrelevantInvariant p q in Refl

  ||| The drop smart constructor is injective
  export
  dropInjective : (th, ph : Th sx sy) -> drop th x === drop ph x -> th === ph
  dropInjective (MkTh i bs p) (MkTh j cs q) eq
    with (cong (pred . bigEnd) eq)
    dropInjective (MkTh i bs p) (MkTh i cs q) eq | Refl
      with (shiftLInjective bs cs 1 (cong encoding eq))
      dropInjective (MkTh i bs p) (MkTh i bs q) eq | Refl | Refl
        = rewrite irrelevantInvariant p q in Refl

  ||| Propositional equality of thinnings is equivalent to propositional
  ||| equality of their encodings (because the Invariant proof is proof irrelevant)
  export
  ThEqEquiv : (th, ph : Th {a} sx sy) ->
              (th.bigEnd === ph.bigEnd, th.encoding === ph.encoding) <=> th === ph
  ThEqEquiv (MkTh i bs p) (MkTh j cs q)
    = MkEquivalence (uncurry $ \ Refl, Refl => rewrite irrelevantInvariant p q in Refl)
                    (\ eq => (cong bigEnd eq, cong encoding eq))

  ||| Boolean equality on thinnings (as defined above) reflects propositional
  ||| equality. Proven using Data.Bool.Decidable.Extra's results.
  export
  eqReflects : (th, ph : Th {a} sx sy) -> Reflects (th === ph) (th == ph)
  eqReflects th@(MkTh i bs p) ph@(MkTh j cs q)
    = mapReflects (ThEqEquiv th ph)
    $ andReflects (reflectsNat i j) (reflectsInteger bs cs)

||| As a consequence equality of thinnings is decidable
export
DecEq (Th sx sy) where
  decEq th ph = toDec (eqReflects th ph)

------------------------------------------------------------------------------
-- Empty and identity thinnings
------------------------------------------------------------------------------

namespace Smart

  ||| Empty thinning
  export
  none : (sy : SnocList a) -> Th [<] sy
  none sy = MkTh (length sy) 0 (none sy)

  ||| Identity thinning
  export
  ones : (sx : SnocList a) -> Th sx sx
  ones sx = let n : Nat; n = length sx in MkTh n (full n) (ones sx)

------------------------------------------------------------------------------
-- And various properties of Thinnings

||| We cannot possibly embed a non-empty snoclist into its tail
export
tooBig : {sx : SnocList a} -> Not (Th (sx :< x) sx)
tooBig th = case view th of
  Keep th x => tooBig th
  Drop th x => tooBig (drop (ones ?) ? *^ th)

||| The thinning from the empty snoclist are proof irrelevant
export
irrelevantNone : (th, ph : Th [<] sx) -> th === ph
irrelevantNone th ph = case view th of
  Done => irrelevantDone ? ?
  Drop th x => case view ph of
    Drop ph x => cong (`drop` x) (irrelevantNone th ph)

||| As a corollary, we can prove that none is equivalent to an inductive
||| definition repeatedly using drop
export
noneIsDrop : none (sx :< x) === drop (none sx) x
noneIsDrop = irrelevantEq $ irrelevantNone ? ?

||| The identity thinning is proof irrelevant
export
irrelevantOnes : (th, ph : Th sx sx) -> th === ph
irrelevantOnes th ph = case view th of
  Done => irrelevantDone ? ?
  Keep th x => case view ph of
    Keep ph x => cong (`keep` x) (irrelevantOnes th ph)
    Drop ph x => void $ tooBig ph
  Drop th x => void $ tooBig th

||| As a corollary, we can prove that ones is equivalent to an inductive
||| definition repeatedly using keep
export
onesIsKeep : (0 sx : SnocList a) -> (0 x : _) -> ones (sx :< x) === keep (ones sx) x
onesIsKeep sx x = irrelevantEq $ irrelevantOnes ? ?

||| Ones is left-neutral wrt composition
export
onesLeftNeutral : (th : Th {a} sx sx) -> (ph : Th sx sy) -> th *^ ph === ph
onesLeftNeutral th ph with (view ph)
  onesLeftNeutral th _ | Done = irrelevantDone ? ?
  onesLeftNeutral th _ | Keep ph x with (view th)
    onesLeftNeutral _ _ | Keep ph x | Keep th x
      = cong (`keep` x) (onesLeftNeutral th ph)
    onesLeftNeutral _ _ | Keep ph x | Drop th x
      = void $ tooBig th
  onesLeftNeutral th _ | Drop ph x = cong (`drop` x) (onesLeftNeutral th ph)

||| Ones is right-neutral wrt composition
export
onesRightNeutral : (th : Th {a} sx sy) -> (ph : Th sy sy) -> th *^ ph === th
onesRightNeutral th ph with (view ph)
  onesRightNeutral th _ | Done = Refl
  onesRightNeutral th _ | Keep ph x with (view th)
    onesRightNeutral _ _ | Keep ph x | Keep th x
      = cong (`keep` x) (onesRightNeutral th ph)
    onesRightNeutral _ _ | Keep ph x | Drop th x
      = cong (`drop` x) (onesRightNeutral th ph)
  onesRightNeutral th _ | Drop ph x = void $ tooBig ph

||| Composition is associative
export
transAssoc : (th : Th {a} sw sx) -> (ph : Th sx sy) -> (ps : Th sy sz) ->
             ((th *^ ph) *^ ps) === (th *^ (ph *^ ps))
transAssoc th ph ps with (view ps)
  transAssoc th ph _ | Done = irrelevantDone ? ?
  transAssoc th ph _ | Keep ps x with (view ph)
    transAssoc th _ _ | Keep ps x | Keep ph x with (view th)
      transAssoc _ _ _ | Keep ps x | Keep ph x | Keep th x
        = rewrite viewKeepUnfold (ph *^ ps) x in
          rewrite viewKeepUnfold (th *^ ph) x in
          rewrite viewKeepUnfold th x in
          cong (`keep` x) (transAssoc th ph ps)
      transAssoc _ _ _ | Keep ps x | Keep ph x | Drop th x
        = rewrite viewKeepUnfold (ph *^ ps) x in
          rewrite viewDropUnfold (th *^ ph) x in
          rewrite viewDropUnfold th x in
          cong (`drop` x) (transAssoc th ph ps)
    transAssoc th _ _ | Keep ps x | Drop ph x
      = rewrite viewDropUnfold (ph *^ ps) x in
        rewrite viewDropUnfold (th *^ ph) x in
        cong (`drop` x) (transAssoc th ph ps)
  transAssoc th ph _ | Drop ps x
    = rewrite viewDropUnfold (ph *^ ps) x in
      cong (`drop` x) (transAssoc th ph ps)

------------------------------------------------------------------------------
-- Intersection & union of supports
------------------------------------------------------------------------------

namespace Smart

  ||| Computing the meet of two source snoclists
  export
  meet : Th sxl sx -> Th sxr sx -> Exists (`Th` sx)
  meet thl thr
    = Evidence ?
    $ MkTh (thl .bigEnd) (thl .encoding .&. thr .encoding)
    $ snd $ Internal.meet (thl .invariant)
    $ rewrite irrelevantSize (thl .invariant) (thr .invariant) in thr .invariant

  ||| Meet is indeed computing a lower bound
  ||| TODO: prove it is the largest such
  export
  isMeet : (th : Th sxl sx) -> (ph : Th sxr sx) ->
           (Th (fst $ meet th ph) sxl, Th (fst $ meet th ph) sxr)
  isMeet th ph = case view th of
    Done => case view ph of
      Done => (done, done)
    Keep th x => case view ph of
      Keep ph x => bimap (`keep` x) (`keep` x) (isMeet th ph)
      Drop ph x => mapFst (`drop` x) (isMeet th ph)
    Drop th x => case view ph of
      Keep ph x => mapSnd (`drop` x) (isMeet th ph)
      Drop ph x => isMeet th ph

  ||| Computing the join of two source snoclists
  export
  join : Th sxl sx -> Th sxr sx -> Exists (`Th` sx)
  join thl thr
    = Evidence ?
    $ MkTh (thl .bigEnd) (thl .encoding .|. thr .encoding)
    $ snd $ Internal.join (thl .invariant)
    $ rewrite irrelevantSize (thl .invariant) (thr .invariant) in thr .invariant

  ||| Join is indeed computing an upper bound
  ||| TODO: prove it is the smallest such
  export
  isJoin : (th : Th sxl sx) -> (ph : Th sxr sx) ->
           (Th sxl (fst $ join th ph), Th sxr (fst $ join th ph))
  isJoin th ph = case view th of
    Done => case view ph of
      Done => (done, done)
    Keep th x => case view ph of
      Keep ph x => bimap (`keep` x) (`keep` x) (isJoin th ph)
      Drop ph x => bimap (`keep` x) (`drop` x) (isJoin th ph)
    Drop th x => case view ph of
      Keep ph x => bimap (`drop` x) (`keep` x) (isJoin th ph)
      Drop ph x => isJoin th ph

||| Concatenate two thinnings
export
(++) : Th sa sb -> Th sx sy -> Th (sa ++ sx) (sb ++ sy)
thl ++ thr = MkTh ? ? (thl.invariant ++ thr.invariant)

||| Like filter but returns a thinning
export
which : (a -> Bool) -> (sy : SnocList a) ->
        (sx : SnocList a ** Th sx sy)
which p [<] = ([<] ** done)
which p (sy :< y) =
  let (sx ** th) = which p sy in
  if p y then (sx :< y ** keep th y)
         else (sx ** drop th y)
