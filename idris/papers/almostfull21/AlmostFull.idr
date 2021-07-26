||| The content of this module is based on the paper
||| Stop when you are Almost-Full
||| -- Adventures in constructive termination
||| by Dimitrios Vytiniotis, and Thierry Coquand

module AlmostFull

import Data.DPair
import Data.Nat
import Data.Nat.Order
import Data.Vect
import Data.Fun
import Data.Rel
import Decidable.Decidable
import Control.WellFounded

%hide Data.Rel.Rel
%hide DPair.DPair.bimap
%hide DPair.Exists.bimap
%hide DPair.Subset.bimap

%default total

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
  = (a : x) -> SecureBy (\ b, c => Either (rel b c) (rel a b)) (f a)

mapSecureBy : {0 p, q : Rel x} -> ((a, b : x) -> p a b -> q a b) ->
      (t : WFT x) -> SecureBy p t -> SecureBy q t
mapSecureBy implies ZT      sec = \ a, b => implies a b (sec a b)
mapSecureBy implies (SUP f) sec = \ a =>
  let implies' = \ a, b => Prelude.bimap (implies _ _) (implies _ _) in
  mapSecureBy implies' (f a) (sec a)

||| An almost full relation is one for which a securing tree exists
0 AlmostFull : Rel x -> Type
AlmostFull rel = (p ** SecureBy rel p)

mapAlmostFull : {0 p, q : Rel x} -> ((a, b : x) -> p a b -> q a b) ->
                AlmostFull p -> AlmostFull q
mapAlmostFull f (p ** sec) = (p ** mapSecureBy f p sec)

record Witness {x : Type} (rel : Rel x) (bound : Nat) (seq : Nat -> x) where
  constructor MkWitness
  index1  : Nat
  index2  : Nat
  ordered : index1 `LT` index2
  beyond  : bound `LTE` index1
  related : rel (seq index1) (seq index2)

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

noInfiniteChain :
  AlmostFull rel -> (seq : Nat -> x) ->
  Witness rel Z seq
noInfiniteChain (t ** sec) seq
  = secured_noInfiniteChain t seq Z sec

accessibleIsAlmostFullFun :
  Decidable 2 [x,x] rel => {v : x} -> Accessible rel v ->
  (w : x) -> Dec (rel w v) -> WFT x
accessibleIsAlmostFullFun (Access rec) w (No _) = ZT
accessibleIsAlmostFullFun @{p} (Access rec) w (Yes prf)
  = SUP $ \ x => accessibleIsAlmostFullFun (rec w prf) x (decide @{p} x w)

accessibleIsAlmostFull :
  Decidable 2 [x,x] rel => {v : x} -> Accessible rel v -> WFT x
accessibleIsAlmostFull @{p} acc
  = SUP (\ w => accessibleIsAlmostFullFun acc w (decide @{p} w v))

secureFromAccFun :
  (dec : Decidable 2 [x,x] rel) => {v : x} -> (acc : Accessible rel v) ->
  (w : x) -> (dec : Dec (rel w  v)) ->
  SecureBy (\x, y => Either (Either (Not (rel y x)) (Not (rel x v)))
                            (Either (Not (rel x w)) (Not (rel w v))))
           (accessibleIsAlmostFullFun acc w dec)

secureFromAccFun      (Access rec) w (No nprf) = \ a, b => Right (Right nprf)
secureFromAccFun @{p} (Access rec) w (Yes prf) = \ a =>
  let p := secureFromAccFun (rec w prf) a (decide @{p} a w)
      f := \a, b =>  bimap (bimap Left Left) (bimap Left Left)
  in mapSecureBy f ? p

secureFromAcc :
  (dec : Decidable 2 [x,x] rel) => {v : x} -> (acc : Accessible rel v) ->
  SecureBy (\x, y => Either (Not (rel y x)) (Not (rel x v)))
           (accessibleIsAlmostFull acc)
secureFromAcc @{p} acc w = secureFromAccFun acc w (decide @{p} w v)

almostFullTree : WellFounded x rel => Decidable 2 [x,x] rel =>
                 x -> WFT x
almostFullTree v = accessibleIsAlmostFull {rel} (wellFounded v)

secureFromWf : (wf : WellFounded x rel) => (dec : Decidable 2 [x,x] rel) =>
  SecureBy (\ x, y => Not (rel y x)) (SUP (almostFullTree @{wf} @{dec}))
secureFromWf v = secureFromAcc (wellFounded v)

almostFullFromWf : WellFounded x rel => Decidable 2 [x,x] rel =>
                   AlmostFull (\ x, y => Not (rel y x))
almostFullFromWf @{wf} @{dec}
  = (SUP (almostFullTree @{wf} @{dec}) ** secureFromWf @{wf} @{dec})

AlmostFullLTE : AlmostFull LTE
AlmostFullLTE = mapAlmostFull (\ a, b => notLTImpliesGTE) almostFullFromWf
