module Thin

import Data.Bits
import Data.Nat

%default total

data Thinning : Nat -> Integer -> SnocList a -> SnocList a -> Type where
  Done : Thinning Z i [<] [<]
  Keep : Thinning n i xs ys -> (0 x : a) ->
         {auto 0 b  : So (      testBit i (S n))} ->
         Thinning (S n) i (xs :< x) (ys :< x)
  Drop : Thinning n i xs ys -> (0 x : a) ->
         {auto 0 nb : So (not $ testBit i (S n))} ->
         Thinning (S n) i xs        (ys :< x)

irrelevantSo : (0 p, q : So b) -> p === q
irrelevantSo Oh Oh = Refl

irrelevantThinning : (th1, th2 : Thinning n i xs ys) -> th1 === th2
irrelevantThinning Done Done = Refl
irrelevantThinning (Keep th1 x {b = b1}) (Keep th2 x {b = b2})
  = cong2 (\ th, b => Keep th x {b}) (irrelevantThinning th1 th2) (irrelevantSo b1 b2)
irrelevantThinning (Drop th1 x {nb = nb1}) (Drop th2 x {nb = nb2})
  = cong2 (\ th, nb => Drop th x {nb}) (irrelevantThinning th1 th2) (irrelevantSo nb1 nb2)
irrelevantThinning (Keep th1 x {b = b1}) (Drop th2 x {nb = nb2})
  = void (soNotToNotSo nb2 b1)
irrelevantThinning (Drop th1 x {nb = nb1}) (Keep th2 x {b = b2})
  = void (soNotToNotSo nb1 b2)

record Th {a : Type} (xs, ys : SnocList a) where
  constructor MkTh
  bigEnd     : Nat
  encoding   : Integer
  0 thinning : Thinning bigEnd encoding xs ys

testSetBitSame : Bits a => (n : Index {a}) -> (i : a) -> So (testBit (setBit i n) n)
testSetBitSame n i = believe_me Oh

-- /!\ We have no guarantee that `Not (m === n)` is not a lie!
testSetBitOther : Bits a => (m, n : Index {a}) -> Not (m === n) ->
                  (i : a) -> testBit (setBit i m) n === testBit i n
testSetBitOther m n neq i = believe_me (Refl {x = testBit i n})

testClearBitSame : Bits a => (n : Index {a}) -> (i : a) -> So (not $ testBit (clearBit i n) n)
testClearBitSame n i = believe_me Oh

testClearBitOther : Bits a => (m, n : Index {a}) -> Not (m === n) ->
                   (i : a) -> testBit (clearBit i m) n === testBit i n
testClearBitOther m n neq i = believe_me (Refl {x = testBit i n})

ltNotEq : {m, n : Nat} -> m `LT` n -> Not (m === n)
ltNotEq lt = case view lt of
  LTZero => absurd
  LTSucc lt => ltNotEq lt . cong pred

setBitPreserve : Thinning m i xs ys -> (0 _ : m `LT` p) -> Thinning m (setBit i p) xs ys
setBitPreserve Done lt = Done
setBitPreserve (Keep th x {b}) lt =
  let 0 eq = testSetBitOther p m (\ eq => ltNotEq lt (sym eq)) i in
  let 0 lt = transitive (lteSuccRight reflexive) lt in
  let 0 b = replace {p = So} (sym eq) b in
  Keep (setBitPreserve th lt) x
setBitPreserve (Drop th x {nb}) lt =
  let 0 eq = testSetBitOther p m (\ eq => ltNotEq lt (sym eq)) i in
  let 0 lt = transitive (lteSuccRight reflexive) lt in
  let 0 nb = replace {p = So . not} (sym eq) nb in
  Drop (setBitPreserve th lt) x

clearBitPreserve : Thinning m i xs ys -> (0 _ : m `LT` p) -> Thinning m (clearBit i p) xs ys
clearBitPreserve Done lt = Done
clearBitPreserve (Keep th x {b}) lt =
  let 0 eq = testClearBitOther p m (\ eq => ltNotEq lt (sym eq)) i in
  let 0 lt = transitive (lteSuccRight reflexive) lt in
  let 0 b = replace {p = So} (sym eq) b in
  Keep (clearBitPreserve th lt) x
clearBitPreserve (Drop th x {nb}) lt =
  let 0 eq = testClearBitOther p m (\ eq => ltNotEq lt (sym eq)) i in
  let 0 lt = transitive (lteSuccRight reflexive) lt in
  let 0 nb = replace {p = So . not} (sym eq) nb in
  Drop (clearBitPreserve th lt) x

done : (i : Integer) -> Th [<] [<]
done i = MkTh Z i Done

keep : Th xs ys -> (0 x : a) -> Th (xs :< x) (ys :< x)
keep (MkTh n i th) x
  = MkTh (S n) (setBit i (S n))
  $ let 0 b = testSetBitSame (S n) i in
    Keep (setBitPreserve {p = S n} th reflexive) x

drop : Th xs ys -> (0 x : a) -> Th xs (ys :< x)
drop (MkTh n i th) x
  = MkTh (S n) (clearBit i (S n))
  $ let 0 nb = testClearBitSame (S n) i in
    Drop (clearBitPreserve {p = S n} th reflexive) x

data View : Th xs ys -> Type where
  VDone : (i : Integer)   -> View (done i)
  VKeep : (th : Th xs ys) -> (0 x : a) -> {auto 0 b : So ?} ->
          View (MkTh (S th.bigEnd) th.encoding (Keep th.thinning x {b}))
  VDrop : (th : Th xs ys) -> (0 x : a) -> {auto 0 nb : So (not ?)} ->
          View (MkTh (S th.bigEnd) th.encoding (Drop th.thinning x {nb}))

record IsDone {a : Type} {i : Integer} {xs, ys : SnocList a} (th : Thinning 0 i xs ys) where
  constructor MkIsDone
  fstIndexIsLin  : xs === [<]
  sndIndexIsLin  : ys === [<]
  thinningIsDone : (th ===)
                 $ replace {p = Thinning 0 i xs} (sym sndIndexIsLin)
                 $ replace {p = flip (Thinning 0 i) [<]} (sym fstIndexIsLin)
                 $ Done

isDone : (th : Thinning 0 i xs ys) -> IsDone th
isDone Done = MkIsDone Refl Refl Refl

record IsKeep
  {a : Type} {n : Nat} {i : Integer} {xs, ys : SnocList a}
  (th : Thinning (S n) i xs ys)
  (b : So (testBit i (S n))) where
  constructor MkIsKeep
  {0 fstIndexTail, sndIndexTail, keptHead : _}
  fstIndexIsSnoc : xs === fstIndexTail :< keptHead
  sndIndexIsSnoc : ys === sndIndexTail :< keptHead
  subThinning    : Thinning n i fstIndexTail sndIndexTail
  thinningIsKeep : (th ===)
                 $ replace {p = Thinning (S n) i xs} (sym sndIndexIsSnoc)
                 $ replace {p = flip (Thinning (S n) i) (sndIndexTail :< keptHead)} (sym fstIndexIsSnoc)
                 $ Keep subThinning keptHead

isKeep : (th : Thinning (S n) i xs ys) -> (b : So (testBit i (S n))) -> IsKeep th b
isKeep (Keep th x {b = b1}) b2 = MkIsKeep Refl Refl th (cong (\ b => Keep th x {b}) (irrelevantSo b1 b2))
isKeep (Drop th x {nb}) b = void (soNotToNotSo nb b)

record IsDrop
  {a : Type} {n : Nat} {i : Integer} {xs, ys : SnocList a}
  (th : Thinning (S n) i xs ys)
  (nb : So (not $ testBit i (S n))) where
  constructor MkIsDrop
  {0 sndIndexTail, keptHead : _}
  sndIndexIsSnoc : ys === sndIndexTail :< keptHead
  subThinning    : Thinning n i xs sndIndexTail
  thinningIsDrop : (th ===)
                 $ replace {p = Thinning (S n) i xs} (sym sndIndexIsSnoc)
                 $ Drop subThinning keptHead

isDrop : (th : Thinning (S n) i xs ys) -> (nb : So (not $ testBit i (S n))) -> IsDrop th nb
isDrop (Drop th x {nb = nb1}) nb2 = MkIsDrop Refl th (cong (\ nb => Drop th x {nb}) (irrelevantSo nb1 nb2))
isDrop (Keep th x {b}) nb = void (soNotToNotSo nb b)

view : (th : Th xs ys) -> View th
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

infixr 5 *^
interface Thable (0 t : SnocList a -> Type) where
  (*^) : {0 as, bs : SnocList a} -> t as -> Th as bs -> t bs

Thable (Th xs) where
  th *^ ph = case view ph of
    VDone i => th
    VDrop ph x => drop (th *^ ph) x
    VKeep ph x => case view th of
      VKeep th x => keep (th *^ ph) x
      VDrop th x => drop (th *^ ph) x
