||| The content of this module is based on the paper
||| Stop when you are Almost-Full
||| -- Adventures in constructive termination
||| by Dimitrios Vytiniotis, and Thierry Coquand

module AlmostFull

import Control.WellFounded

import Data.DPair
import Data.Either
import Data.Either.Relation
import Data.Fun
import Data.List.Elem
import Data.Nat
import Data.Nat.Order
import Data.Nat.Order.Strict
import Data.Rel
import Data.Relation
import Data.Relation.Closure.ReflexiveTransitive
import Data.Relation.Closure.Transitive
import Data.Vect

import Decidable.Decidable
import Decidable.Equality
import Decidable.Order.Strict

%hide Data.Rel.Rel
%hide DPair.DPair.uncurry
%hide DPair.DPair.bimap
%hide DPair.Exists.uncurry
%hide DPair.Exists.bimap
%hide DPair.Subset.bimap

%default total

------------------------------------------------------------------------
-- Basic types
------------------------------------------------------------------------

||| A well-founded tree on `x` can be thought of a winning strategy
||| in a game.
data WFT : Type -> Type where
  ||| The game has finished and we have won
  ZT  : WFT x
  ||| The opponent can provide a next `x` value and we'll know how to respond
  SUP : (x -> WFT x) -> WFT x

||| A relation is secured by a tree if the tree is a witness that every infinite
||| sequence has two related elements.
0 SecureBy : Rel x -> WFT x -> Type
SecureBy rel ZT
  -- If the tree is empty then we should already have reached a step where
  -- the relation is total
  = (a, b : x) -> rel a b
SecureBy rel (SUP f)
  -- If it is non-empty then given the head of that sequence, we will:
  -- * either find two related elements in the tail of the sequence
  -- * or be able to find an element related to it in the tail of the sequence
  -- That is to say the modified relation is secured by the subtree
  = (a : x) -> SecureBy (Or rel (const . rel a)) (f a)

||| An almost full relation is one for which a securing tree exists
export
0 AlmostFull : Rel x -> Type
AlmostFull rel = (p ** SecureBy rel p)

------------------------------------------------------------------------
-- Functoriality wrt the relation
------------------------------------------------------------------------

||| If a relation can be embedded into another then a tree securing the
||| tighter relation is also securing the other.
mapSecureBy : (p ~> q) ->
      (t : WFT x) -> SecureBy p t -> SecureBy q t
mapSecureBy implies ZT      sec = \ a, b => implies (sec a b)
mapSecureBy implies (SUP f) sec = \ a =>
  mapSecureBy (bimap implies implies) (f a) (sec a)

forSecureBy : (t : WFT x) -> SecureBy p t ->
              (p ~> q) -> SecureBy q t
forSecureBy t sec f = mapSecureBy f t sec

||| If a relation can be embedded into another and if the tighter relation
||| is Almost full then so is the one it embeds into.
export
mapAlmostFull : (p ~> q) -> AlmostFull p -> AlmostFull q
mapAlmostFull f (p ** sec) = (p ** mapSecureBy f p sec)

------------------------------------------------------------------------
-- Decidable & well founded implies negation is almost full
------------------------------------------------------------------------

||| A witness is a proof that we can find two indices bigger than the given
||| bound such that the values they respectively point to in the sequence seq
||| are related by relation rel.
record Witness {x : Type} (rel : Rel x) (bound : Nat) (seq : Nat -> x) where
  constructor MkWitness
  index1  : Nat
  index2  : Nat
  ordered : index1 `LT` index2
  beyond  : bound `LTE` index1
  related : rel (seq index1) (seq index2)

||| A relation secured by a tree can associate a witness to any sequence
secured_noInfiniteChain :
  (p : WFT x) -> (seq : Nat -> x) ->
  (k : Nat) -> SecureBy rel p ->
  Witness rel k seq
secured_noInfiniteChain ZT      seq k sec
  = MkWitness k (S k) (reflexive {rel = LTE}) (reflexive {rel = LTE}) (sec _ _)
secured_noInfiniteChain (SUP f) seq k sec
  = case secured_noInfiniteChain (f (seq k)) seq (S k) (sec (seq k)) of
      (MkWitness index1 index2 ordered beyond related) => either
         (MkWitness index1 index2 ordered (lteSuccLeft beyond))
         (MkWitness k index1 beyond (reflexive {rel = LTE}))
         related

||| An almost full relation can find a witness in any sequence
noInfiniteChain :
  AlmostFull rel -> (seq : Nat -> x) ->
  Witness rel Z seq
noInfiniteChain (t ** sec) seq
  = secured_noInfiniteChain t seq Z sec

-- auxiliary function
accessibleIsAlmostFullFun :
  Decidable 2 [x,x] rel => {v : x} -> Accessible rel v ->
  (w : x) -> Dec (rel w v) -> WFT x
accessibleIsAlmostFullFun (Access rec) w (No _) = ZT
accessibleIsAlmostFullFun @{p} (Access rec) w (Yes prf)
  = SUP $ \ x => accessibleIsAlmostFullFun (rec w prf) x (decide @{p} x w)

||| An accessible element wrt a relation has a well founded tree on
||| the relation's carrier
accessibleIsAlmostFull :
  Decidable 2 [x,x] rel => {v : x} -> Accessible rel v -> WFT x
accessibleIsAlmostFull @{p} acc
  = SUP (\ w => accessibleIsAlmostFullFun acc w (decide @{p} w v))

-- auxiliary function
secureFromAccFun :
  (dec : Decidable 2 [x,x] rel) => {v : x} -> (acc : Accessible rel v) ->
  (w : x) -> (dec : Dec (rel w  v)) ->
  SecureBy (\x, y => Either (Either (Not (rel y x)) (Not (rel x v)))
                            (Either (Not (rel x w)) (Not (rel w v))))
           (accessibleIsAlmostFullFun acc w dec)

secureFromAccFun      (Access rec) w (No nprf) = \ a, b => Right (Right nprf)
secureFromAccFun @{p} (Access rec) w (Yes prf) = \ a =>
  let p := secureFromAccFun (rec w prf) a (decide @{p} a w)
  in mapSecureBy (bimap (bimap Left Left) (bimap Left Left)) ? p

||| The well founded tree associated to an element accessible wrt rel
||| is securing the relation rel
secureFromAcc :
  (dec : Decidable 2 [x,x] rel) => {v : x} -> (acc : Accessible rel v) ->
  SecureBy (Or (Not (flip rel)) (Not (\ x, y => rel x v)))
           (accessibleIsAlmostFull acc)
secureFromAcc @{p} acc w = secureFromAccFun acc w (decide @{p} w v)

||| A well founded relation has an associated well founded tree on its carrier
almostFullTree : WellFounded x rel => Decidable 2 [x,x] rel =>
                 x -> WFT x
almostFullTree v = accessibleIsAlmostFull {rel} (wellFounded v)

||| The well founded tree associated to a well founded relation is securing it
secureFromWf : (wf : WellFounded x rel) => (dec : Decidable 2 [x,x] rel) =>
  SecureBy (Not (flip rel)) (SUP (almostFullTree @{wf} @{dec}))
secureFromWf v = secureFromAcc (wellFounded v)

||| The negation of a well founded relation is Almost full
almostFullFromWf : WellFounded x rel => Decidable 2 [x,x] rel =>
                   AlmostFull (\ x, y => Not (rel y x))
almostFullFromWf @{wf} @{dec}
  = (SUP (almostFullTree @{wf} @{dec}) ** secureFromWf @{wf} @{dec})

------------------------------------------------------------------------
-- Example

||| Example: LTE on natural numbers is Almost Full because
||| 1. LT is well founded
||| 2. The negation LT embeds into LTE
export
almostFullLTE : AlmostFull LTE
almostFullLTE = mapAlmostFull notLTImpliesGTE almostFullFromWf

------------------------------------------------------------------------
-- Almostfull implies well founded for well quasi order (WQO)
------------------------------------------------------------------------

accessibleFromAF :
  (p : WFT x) -> (v : x) ->
  ((a, b : x) -> RTList t b v -> Not (TList t a b, rel b a)) ->
  SecureBy rel p -> Accessible t v
accessibleFromAF ZT      v prop sec
  = Access $ \ w, twv => absurd (prop w v [] ([twv], sec v w))
accessibleFromAF (SUP f) v prop sec
  = Access $ \ w, twv =>
    let prop' = \ a, b, tbw => uncurry $ \ tab, r =>
                either (\ rba => prop a b (tbw ++ [twv]) (tab, rba))
                       (\ rvb => prop b v [] (tbw ++ [twv], rvb))
                       r
    in accessibleFromAF (f v) w prop' (sec v)

public export
0 NoInfiniteDescent : (t, rel : Rel a) -> Type
NoInfiniteDescent t rel = ((x, y : a) -> Not (And (TList t) (flip rel)) x y)

export
noInfiniteDescent :
  StrictPreorder z tz =>
  (transz :  {a, b, c : _} -> tz a b -> relz b c -> tz a c) ->
  NoInfiniteDescent tz relz
noInfiniteDescent transz z1 z2 (ts, rel)
    = irreflexive {rel = tz} (transz (tlist ts) rel)

export
wellFoundedFromAF :
  AlmostFull rel ->
  NoInfiniteDescent t rel ->
  (v : x) -> Accessible t v
wellFoundedFromAF (p ** sec) prop v
  = accessibleFromAF p v (\ a, b, _, p => prop a b p) sec

export
wellFoundedFromAFWQO :
  Transitive x rel => AlmostFull rel ->
  (v : x) -> Accessible (\ x, y => (rel x y, Not (rel y x))) v
wellFoundedFromAFWQO af v = wellFoundedFromAF af prop v where

  0 STRICT : Rel x
  STRICT x y = (rel x y, Not (rel y x))

  tcontra : TList STRICT ~> Not (flip rel)
  tcontra ((ray, nrya) :: rs) rba = nrya $ tlist (map fst rs ++ [rba])

  prop : (a, b : x) -> Not (And (TList STRICT) (flip rel)) a b
  prop a b (ts, rba) = tcontra ts rba

-- TODO: move to base's `Control.Wellfounded`
export
map : (p ~> q) -> {x : a} -> Accessible q x -> Accessible p x
map f (Access rec) = Access $ \ y, pyx => map f (rec y (f pyx))

------------------------------------------------------------------------
-- Example

||| Example: LT on natural numbers is well founded because
||| 1. LTE is almost full
||| 2. LT embeds into LTE & the negation of its symmetric
export
wellFoundedLT : (n : Nat) -> Accessible LT n
wellFoundedLT n
  = map (\ ltxy => (lteSuccLeft ltxy
                   , succNotLTEpred . transitive {rel = LTE} ltxy)
        )
  $ wellFoundedFromAFWQO almostFullLTE n

------------------------------------------------------------------------
-- Induction principle for almost full relations
------------------------------------------------------------------------

public export
0 Rec : Rel a -> (a -> Type) -> Type
Rec t p = (x : a) -> (ih : (y : a) -> t y x -> p y) -> p x

export
almostFullInduction :
  AlmostFull rel ->
  NoInfiniteDescent t rel ->
  Rec t p -> (v : a) -> p v
almostFullInduction af prop acc v
  = accInd acc v (wellFoundedFromAF af prop v)

------------------------------------------------------------------------
-- Example

fib : Nat -> Nat
fib = almostFullInduction almostFullLTE inter $ \x, ih => case x of
  0       => 1
  1       => 1
  S (S n) => ih (S n) (reflexive {rel = LTE})
           + ih n (lteSuccRight $ reflexive {rel = LTE})

  where

    inter : (x, y : Nat) -> Not (And (TList LT) GTE) x y
    inter x y (lts, lte) = succNotLTEpred
                         $ transitive {rel = LTE} (tlist lts) lte

------------------------------------------------------------------------
-- Almostfull is closed under unions
------------------------------------------------------------------------

secureByUnionL : (t : WFT x) -> SecureBy p t -> SecureBy (Or p q) t
secureByUnionL = mapSecureBy Left

almostFullUnionL : AlmostFull p -> AlmostFull (Or p q)
almostFullUnionL (t ** sec) = (t ** secureByUnionL t sec)

secureByUnionR : (t : WFT x) -> SecureBy q t -> SecureBy (Or p q) t
secureByUnionR = mapSecureBy Right

almostFullUnionR : AlmostFull q -> AlmostFull (Or p q)
almostFullUnionR (t ** sec) = (t ** secureByUnionR t sec)

export
almostFullUnion : Either (AlmostFull p) (AlmostFull q) -> AlmostFull (Or p q)
almostFullUnion = either almostFullUnionL almostFullUnionR

------------------------------------------------------------------------
-- Almostfull is closed under intersections
------------------------------------------------------------------------

||| seq0 secures the intersection of nullary relations secured by p and q
||| respectively
seq0 : (p, q : WFT x) -> WFT x
seq0 ZT      q = q
seq0 (SUP f) q = SUP $ \ x => seq0 (f x) q

seqNullaryAndAux : (p, q : WFT x) ->
  SecureBy (Or rel (Const a)) p ->
  SecureBy (Or rel (Const b)) q ->
  SecureBy (Or rel (Const (a, b))) (p `seq0` q)
seqNullaryAndAux ZT      q secp secq
  = forSecureBy q secq
  $ either Left
  $ \ b => either Left (Right . (,b)) (secp _ _)
seqNullaryAndAux (SUP f) q secp secq
  = \ a => mapSecureBy (either (bimap Left Left) (Left . Right)) (seq0 (f a) q)
  $ seqNullaryAndAux (f a) q
     (mapSecureBy (either (mapFst Left) (mapFst Right)) (f a) (secp a))
     (mapSecureBy (mapFst Left) q secq)

seqNullaryAnd : (p, q : WFT x) ->
  SecureBy (Const a) p ->
  SecureBy (Const b) q ->
  SecureBy (Const (a, b)) (p `seq0` q)
seqNullaryAnd p q secp secq
  = mapSecureBy (either absurd id) _
  $ seqNullaryAndAux {rel = Const Void} p q
     (mapSecureBy Right p secp)
     (mapSecureBy Right q secq)

seq1 : (p, q : WFT x) -> WFT x
seq1 ZT q = q
seq1 p ZT = p
seq1 p@(SUP f) q@(SUP g)
  = SUP (\ x => seq0 (seq1 (f x) q) (seq1 p (g x)))

seqUnaryAndAux :
  {0 a, b : x -> Type} ->
  (p, q : WFT x) ->
  SecureBy (Or rel (\ x, _ => a x)) p ->
  SecureBy (Or rel (\ x, _ => b x)) q ->
  SecureBy (Or rel (\ x, _ => (a x, b x))) (p `seq1` q)
seqUnaryAndAux ZT q secp secq
  = forSecureBy q secq
  $ either Left
  $ \ b => mapSnd (, b) (secp _ _)
seqUnaryAndAux p@(SUP _) ZT secp secq
  = forSecureBy p secp
  $ either Left
  $ \ a => mapSnd (a,) (secq _ _)
seqUnaryAndAux p@(SUP f) q@(SUP g) secp secq = \ v =>
  let ih1  := seqUnaryAndAux (f v) q
                (forSecureBy (f v) (secp v)
                  $ either (mapSnd Left) (Right . Right))
                secq
      ih2  := seqUnaryAndAux p (g v)
                secp
                (forSecureBy (g v) (secq v)
                  $ either (mapSnd Left) (Right . Right))
  in mapSecureBy (either (either Left (Right . Left)) (Right . Right)) ?
   $ seqNullaryAndAux (seq1 (f v) q) (seq1 p (g v))
       (forSecureBy ? ih1
         $ either (Left . Left . Left)
         $ uncurry $ \ e, bx =>
           either (\ ax => Left $ Left $ Right $ MkPair ax bx)
                  (mapFst Right)
                  e)
       (forSecureBy ? ih2
         $ either (Left . Left . Left)
         $ uncurry $ \ax, e =>
           either (\ bx => Left $ Left $ Right $ MkPair ax bx)
                  (mapFst Right)
                  e)

seqUnaryAnd :
  {0 a, b : x -> Type} ->
  (p, q : WFT x) ->
  SecureBy (\ x, _ => a x) p ->
  SecureBy (\ x, _ => b x) q ->
  SecureBy (\ x, _ => (a x, b x)) (p `seq1` q)
seqUnaryAnd p q secp secq
  = mapSecureBy (either absurd id) _
  $ seqUnaryAndAux {rel = Const Void} p q
     (mapSecureBy Right p secp)
     (mapSecureBy Right q secq)

seq2 : (p, q : WFT x) -> WFT x
seq2 ZT q = q
seq2 p ZT = p
seq2 p@(SUP f) q@(SUP g)
  = SUP $ \ x => seq1 (seq2 (f x) q) (seq2 p (g x))

seqBinaryAndAux :
  (p, q : WFT x) ->
  SecureBy (Or rel a) p ->
  SecureBy (Or rel b) q ->
  SecureBy (Or rel (And a b)) (p `seq2` q)
seqBinaryAndAux ZT q secp secq
  = forSecureBy q secq
  $ either Left
  $ \bxy => mapSnd (, bxy) (secp _ _)
seqBinaryAndAux p@(SUP f) ZT secp secq
  = forSecureBy p secp
  $ either Left
  $ \ axy => mapSnd (axy,) (secq _ _)
seqBinaryAndAux p@(SUP f) q@(SUP g) secp secq = \ v =>
  let ih1  := seqBinaryAndAux (f v) q
                (forSecureBy (f v) (secp v)
                  $ either (mapSnd Left) (Right . Right))
                secq
      ih2  := seqBinaryAndAux p (g v)
                secp
                (forSecureBy (g v) (secq v)
                  $ either (mapSnd Left) (Right . Right))
  in mapSecureBy (either (either Left (Right . Left)) (Right . Right)) ?
   $ seqUnaryAndAux (seq2 (f v) q) (seq2 p (g v))
       (forSecureBy ? ih1
         $ either (Left . Left . Left)
         $ uncurry $ \ e, bx =>
           either (\ ax => Left $ Left $ Right $ MkPair ax bx)
                  (mapFst Right)
                  e)
       (forSecureBy ? ih2
         $ either (Left . Left . Left)
         $ uncurry $ \ax, e =>
           either (\ bx => Left $ Left $ Right $ MkPair ax bx)
                  (mapFst Right)
                  e)

secureByIntersection :
  (p, q : WFT x) ->
  SecureBy a p ->
  SecureBy b q ->
  SecureBy (And a b) (p `seq2` q)
secureByIntersection p q secp secq
  = mapSecureBy (either absurd id) _
  $ seqBinaryAndAux {rel = Const Void} p q
     (mapSecureBy Right p secp)
     (mapSecureBy Right q secq)

export
almostFullIntersection : AlmostFull p -> AlmostFull q -> AlmostFull (And p q)
almostFullIntersection (p ** secp) (q ** secq)
  = (? ** secureByIntersection p q secp secq)

------------------------------------------------------------------------
-- Almostfull is closed under `on`
------------------------------------------------------------------------

contra : (y -> x) -> WFT x -> WFT y
contra f ZT = ZT
contra f (SUP w) = SUP $ \ y => contra f (w (f y))

secureByContra : (f : y -> x) -> (p : WFT x) ->
                 SecureBy rel p -> SecureBy (rel `on` f) (contra f p)
secureByContra f ZT      sec = \a, b => sec (f a) (f b)
secureByContra f (SUP g) sec = \ a => secureByContra f (g (f a)) (sec (f a))

export
almostFullOn : (f : y -> x) -> AlmostFull rel -> AlmostFull (rel `on` f)
almostFullOn f (p ** sec) = (? ** secureByContra f p sec)

------------------------------------------------------------------------
-- Example

TFlip : Rel (Nat, Nat)
TFlip (x1,x2) (y1,y2) = (x1 `LTE` y2, x2 `LT` y1)

RFlip : Rel (Nat, Nat)
RFlip = LTE `on` (\x => fst x + snd x)

SFlip : Rel (Nat, Nat)
SFlip = LT `on` (\ x => fst x + snd x)

Transitive (Nat, Nat) SFlip where
  transitive = transitive {rel = LT}

TtoS : {x, y : (Nat, Nat)} -> TFlip x y -> SFlip x y
TtoS {x = (x1, x2)} {y = (y1, y2)} t
  = rewrite plusCommutative x1 x2 in
    plusLteMonotone (snd t) (fst t)

AlmostFullRFlip : AlmostFull RFlip
AlmostFullRFlip = almostFullOn ? almostFullLTE

||| The function we want to write without assert_total
flip1 : (Nat, Nat) -> Nat
flip1 (0, _) = 1
flip1 (_, 0) = 1
flip1 (S x, S y) = assert_total $ flip1 (S y, x)

||| The almostFullInduction version
flip1' : (Nat, Nat) -> Nat
flip1' = almostFullInduction AlmostFullRFlip {p = \_=> Nat} prf rec where

  rec : (x : (Nat, Nat)) ->
        ((y : (Nat, Nat)) -> TFlip y x -> Nat) -> Nat
  rec (0, _)     ih = 1
  rec (_, 0)     ih = 1
  rec (S x, S y) ih = ih (S y, x) (reflexive {rel = LTE}, reflexive {rel = LTE})

  prf : NoInfiniteDescent TFlip RFlip
  prf (x1, x2) (y1, y2) (txys, ryx) =
    let rxy = tlist $ map {q = SFlip} TtoS txys in
    let p = transitive {rel = LTE} rxy ryx in
    -- weird workaround
    let el = irreflexive {rel = LT} in el p

------------------------------------------------------------------------
-- Almostfull is true of finite types
------------------------------------------------------------------------

boolTree : WFT Bool
boolTree = SUP $ \ x => SUP $ \ y => ZT

secureByBool : SecureBy (===) AlmostFull.boolTree
secureByBool False False c     d = Right (Right Refl)
secureByBool False True  False d = Left (Right Refl)
secureByBool False True  True  d = Right (Left Refl)
secureByBool True  False False d = Right (Left Refl)
secureByBool True  False True  d = Left (Right Refl)
secureByBool True  True  c     d = Right (Right Refl)

almostFullBool : AlmostFull ((===) {a = Bool})
almostFullBool = (boolTree ** secureByBool)

------------------------------------------------------------------------
-- Almostfull is closed under products
------------------------------------------------------------------------

secureByPair :
  {p : WFT x} -> {q : WFT y} ->
  SecureBy relp p -> SecureBy relq q ->
  SecureBy (And (relp `on` Builtin.fst) (relq `on` Builtin.snd))
           (seq2 (contra Builtin.fst p) (contra Builtin.snd q))
secureByPair secp secq
  = secureByIntersection ? ?
      (secureByContra ? ? secp)
      (secureByContra ? ? secq)

export
almostFullPair : AlmostFull p -> AlmostFull q ->
                 AlmostFull (And (p `on` Builtin.fst) (q `on` Builtin.snd))
almostFullPair (p ** secp) (q ** secq) = (? ** secureByPair secp secq)

almostFullProj1 : AlmostFull p -> AlmostFull (p `on` Builtin.fst)
almostFullProj1 (p ** secp) = (? ** secureByContra ? ? secp)

------------------------------------------------------------------------
-- From closure under pairs we can get lexicographic induction
------------------------------------------------------------------------

data Lexico : Rel x -> Rel y -> Rel (x, y) where
  Fst : {0 relx : Rel x} ->
        relx x1 x2 -> Lexico relx rely (x1, y1) (x2, y2)
  Snd : {0 rely : Rel y} ->
        x1 === x2 -> rely y1 y2 -> Lexico relx rely (x1, y1) (x2, y2)

bimap : (p ~> p') -> (q ~> q') -> Lexico p q ~> Lexico p' q'
bimap f g (Fst p)    = Fst (f p)
bimap f g (Snd eq q) = Snd eq (g q)

stepDown : TList (Lexico p q) ~> Lexico (TList p) (TList q)
stepDown (t :: ts) = go (bimap (:: []) (:: []) t) ts where

  go : Lexico (TList p) (TList q) x y ->
       RTList (Lexico p q) y z ->
       Lexico (TList p) (TList q) x z
  go acc           []                 = acc
  go (Fst ps)      (Fst p      :: ts) = go (Fst (ps :< p)) ts
  go (Fst ps)      (Snd Refl _ :: ts) = go (Fst ps) ts
  go (Snd Refl qs) (Fst p      :: ts) = go (Fst [p]) ts
  go (Snd Refl qs) (Snd eq q   :: ts) = go (Snd eq (qs :< q)) ts

(Transitive x relx, Transitive y rely) =>
  Transitive (x, y) (Lexico relx rely) where
  transitive p q = bimap tlist tlist $ stepDown [p, q]

lexicographic :
  AlmostFull relx -> AlmostFull rely ->
  NoInfiniteDescent tx relx ->
  NoInfiniteDescent ty rely ->
  Rec (Lexico tx ty) p -> (v : (x, y)) -> p v
lexicographic afx afy prfx prfy = almostFullInduction af prf where

  0 T : Rel (x, y)
  T = Lexico tx ty

  0 R : Rel (x, y)
  R = And (relx `on` Builtin.fst) (rely `on` Builtin.snd)

  af : AlmostFull R
  af = almostFullPair afx afy

  prf : NoInfiniteDescent T R
  prf (x1, x2) (y1, y2) (ts, (p, q)) = case stepDown ts of
    Fst   ps => prfx ? ? (ps, p)
    Snd _ qs => prfy ? ? (qs, q)

lexicographicSPO :
  (StrictPreorder x tx, StrictPreorder y ty) =>
  (transx : {a, b, c : _} -> tx a b -> relx b c -> tx a c) ->
  (transy : {a, b, c : _} -> ty a b -> rely b c -> ty a c) ->
  AlmostFull relx -> AlmostFull rely ->
  Rec (Lexico tx ty) p -> (v : (x, y)) -> p v
lexicographicSPO transx transy afx afy
  = lexicographic afx afy
      (noInfiniteDescent transx)
      (noInfiniteDescent transy)

------------------------------------------------------------------------
-- Example


||| The function we want to write without assert_total
flex : (Nat, Nat) -> Nat
flex (0, _) = 1
flex (_, 0) = 1
flex (S x, S y) = assert_total $ flex (x, 2+y) + flex (S x, y)

||| Deploying lexicographic ordering:
flex' : (Nat, Nat) -> Nat
flex' = lexicographicSPO
          (transitive {rel = LTE}) (transitive {rel = LTE})
          almostFullLTE almostFullLTE
          rec

  where

  rec : Rec (Lexico LT LT) (\_ => Nat)
  rec (0, _)     ih = 1
  rec (_, 0)     ih = 1
  rec (S x, S y) ih = ih (x, 2+y) (Fst (reflexive {rel = LTE}))
                    + ih (S x, y) (Snd Refl (reflexive {rel = LTE}))

------------------------------------------------------------------------
-- Almostfull is closed under sums
------------------------------------------------------------------------

lsum : WFT x -> WFT (Either x y)
lsum ZT = SUP $ \_ => SUP $ \_ => ZT
lsum (SUP f) = SUP $ \ xy => case xy of
  Left x => lsum (f x)
  Right y => SUP $ \ xy' => case xy' of
    Left x => lsum (f x)
    Right y' => ZT

secureByLsum : (p : WFT x) -> SecureBy rel p ->
               SecureBy (Pointwise rel (Const ())) (lsum p)
secureByLsum ZT sec = go where

  go : (a, b, c, d : Either x y) ->
       Either (Either (Pointwise rel (Const ()) c d)
                      (Pointwise rel (Const ()) a c))
              (Either (Pointwise rel (Const ()) b c)
                      (Pointwise rel (Const ()) a b))
  go (Left a)  b         (Left c)  d = Left (Right (PLeft (sec a c)))
  go (Right a) (Left b)  (Left c)  d = Right (Left (PLeft (sec b c)))
  go (Right a) (Right b) (Left c)  d = Right (Right (PRight ()))
  go (Left a)  (Left z)  (Right c) d = Right (Right (PLeft (sec a z)))
  go (Left a)  (Right z) (Right c) d = Right (Left (PRight ()))
  go (Right a) b         (Right c) d = Left (Right (PRight ()))

secureByLsum (SUP f) sec = \case
  (Left a) => mapSecureBy rearrange ? (secureByLsum (f a) (sec a))
  (Right b) => \case
    (Left a) => mapSecureBy rearrange2 ? (secureByLsum (f a) (sec a))
    (Right b') => \a, y => Right (Right (PRight ()))

  where

    rearrange : {0 a : x} ->
                Pointwise (Or rel (\ i, _ => rel a i)) (Const ()) ~>
                Or (Pointwise rel (Const ()))
                   (\ i, _=> Pointwise rel (Const ()) (Left a) i)
    rearrange (PLeft prf)  = bimap PLeft PLeft prf
    rearrange (PRight prf) = Left (PRight prf)

    rearrange2 : Pointwise (Or rel (\ i, j => rel a i)) (Const ()) i j ->
                 Either (Either (Pointwise rel (Const ()) i j)
                                (Pointwise rel (Const ()) (Right b) i))
                        (Either (Pointwise rel (Const ()) (Left a) i)
                                (Pointwise rel (Const ()) (Right b) (Left a)))
    rearrange2 (PLeft (Left prf))  = Left (Left (PLeft prf))
    rearrange2 (PLeft (Right prf)) = Right (Left (PLeft prf))
    rearrange2 (PRight prf)        = Left (Left (PRight prf))

rsum : WFT y -> WFT (Either x y)
rsum = contra mirror . lsum

secureByRsum : (p : WFT y) -> SecureBy rel p ->
               SecureBy (Pointwise rel (Const ()) `on` Either.mirror) (rsum p)
secureByRsum p sec = secureByContra mirror (lsum p) (secureByLsum p sec)

almostFullLsum : AlmostFull p -> AlmostFull (Pointwise p (Const ()))
almostFullLsum (p ** secp) = (? ** secureByLsum p secp)

almostFullRsum : AlmostFull p -> AlmostFull (Pointwise (Const ()) p)
almostFullRsum (p ** secp)
  = (? ** mapSecureBy comirror ? $ secureByRsum p secp)

almostFullSum : AlmostFull p -> AlmostFull q -> AlmostFull (Pointwise p q)
almostFullSum afp afq
  = mapAlmostFull (pointwiseBimap fst snd . uncurry and)
  $ almostFullIntersection (almostFullLsum afp) (almostFullRsum afq)

------------------------------------------------------------------------
-- Example

gnlex : (Nat, Nat) -> Nat
gnlex (0, _) = 1
gnlex (_, 0) = 1
gnlex (S m, S n) = assert_total $ gnlex (S n, n) + S (gnlex (S n, m))
