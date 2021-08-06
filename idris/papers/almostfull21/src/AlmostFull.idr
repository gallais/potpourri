||| The content of this module is based on the paper
||| Stop when you are Almost-Full
||| -- Adventures in constructive termination
||| by Dimitrios Vytiniotis, and Thierry Coquand

module AlmostFull

import Data.DPair
import Data.Nat
import Data.Nat.Order
import Data.Nat.Order.Strict
import Data.Vect
import Data.Fun
import Data.Rel
import Decidable.Decidable
import Control.WellFounded
import Data.Relation
import Data.Relation.Closure.Transitive
import Data.Relation.Closure.ReflexiveTransitive

%hide Data.Rel.Rel
%hide DPair.DPair.bimap
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

||| Example: LTE on natural numbers is Almost Full because
||| 1. LT is well founded
||| 2. The negation LT embeds into LTE
AlmostFullLTE : AlmostFull LTE
AlmostFullLTE = mapAlmostFull notLTImpliesGTE almostFullFromWf

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

wellFoundedFromAF :
  AlmostFull rel ->
  ((a, b : x) -> Not (TList t a b, rel b a)) ->
  (v : x) -> Accessible t v
wellFoundedFromAF (p ** sec) prop v
  = accessibleFromAF p v (\ a, b, _, p => prop a b p) sec

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
map : (p ~> q) -> {x : a} -> Accessible q x -> Accessible p x
map f (Access rec) = Access $ \ y, pyx => map f (rec y (f pyx))

||| Example: LT on natural numbers is well founded because
||| 1. LTE is almost full
||| 2. LT embeds into LTE & the negation of its symmetric
wellFoundedLT : (n : Nat) -> Accessible LT n
wellFoundedLT n
  = map (\ ltxy => (lteSuccLeft ltxy
                   , succNotLTEpred . transitive {rel = LTE} ltxy)
        )
  $ wellFoundedFromAFWQO AlmostFullLTE n

almostFullInduction :
  AlmostFull rel ->
  ((x, y : a) -> Not (And (TList t) (flip rel)) x y) ->
  {p : a -> Type} ->
  (acc : (x : a) -> (ih : (y : a) -> t y x -> p y) -> p x) ->
  (v : a) -> p v
almostFullInduction af prop acc v
  = accInd acc v (wellFoundedFromAF af prop v)


fib : Nat -> Nat
fib = almostFullInduction AlmostFullLTE inter $ \x, ih => case x of
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
  $ \ b => either Left (Right . (,b)) (secp _ _)
seqUnaryAndAux p@(SUP _) ZT secp secq
  = forSecureBy p secp
  $ either Left
  $ \ a => either Left (Right . (a,)) (secq _ _)
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
         $ Prelude.uncurry $ \ e, bx =>
           either (\ ax => Left $ Left $ Right $ MkPair ax bx)
                  (mapFst Right)
                  e)
       (forSecureBy ? ih2
         $ either (Left . Left . Left)
         $ Prelude.uncurry $ \ax, e =>
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
