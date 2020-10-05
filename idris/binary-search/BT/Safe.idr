module BT.Safe

import Data.Buffer
import Data.Int.Order
import Data.DPair
import Data.Array.ReadOnly
import Data.Order
import Data.Order.Extended

%default total

public export
Rel : Type -> Type
Rel a = a -> a -> Type

||| A type corresponding to a check on whether a subarray is empty
public export
EmptinessCheck : SubArray arr -> Type
EmptinessCheck sub =
  let bnds : (Int, Int); bnds = boundaries sub
      start : Int; start = fst bnds
      finish : Int; finish = snd bnds
  in Either (LT start finish) (GTE start finish)

public export
emptinessCheck : (sub : SubArray arr) -> EmptinessCheck sub
emptinessCheck sub =
  let bnds : (Int, Int); bnds = boundaries sub in
  decide_LT_GTE (fst bnds) (snd bnds)

mutual

  ||| The inductive type `BT'` proves that a given subarray is sorted.
  ||| @lt  is the strict ordering used for this notion of being sorted
  ||| @arr is the underlying physical (read-only) array
  ||| @sub is the sub array we are focusing on
  ||| And the values in the subarray are contained between two (exclusive) bounds:
  ||| @lbV is the lower bound
  ||| @ubV is the upper bound
  ||| Finally, a tag:
  ||| @tag helps Idris see that the two constructors are disjoint
  data BT' : (lt : Rel a) ->
             {arr : Array a} -> (sub : SubArray arr) ->
             (lbV, ubV : Extended a) ->
             (tag : EmptinessCheck sub) ->
             Type where
    ||| If the range [lbI..ubI] is empty then the proof is trivial
    Empty : {0 sub : SubArray arr} -> (prf : _) -> BT' lt sub lbV ubV (Right prf)

    ||| Otherwise the expect the value at position `middle lbI ubI`
    ||| to be bounded by `lbV` and `ubV` and the subarrays to the
    ||| left and to the right of this middle point to be sorted too.
    Node  : {a : Type} -> {lt : Rel a} -> {arr : Array a} -> {sub : SubArray arr} ->
            let bnds : (Int, Int); bnds = boundaries sub in
            (prf : LT (fst bnds) (snd bnds)) ->
            -- value in the middle position
            {v : a} -> ValueAt arr (middle sub) v ->
            {lbV, ubV : Extended a} ->
            ExtendedLT lt lbV (Lift v) -> ExtendedLT lt (Lift v) ubV ->
            let cuts : (SubArray arr, SubArray arr); cuts = cut sub (middleInRange prf) in
            -- each half is sorted too
            BT lt (fst cuts) lbV (Lift v) ->
            BT lt (snd cuts) (Lift v) ubV ->
            -- whole subarray is sorted
            BT' lt {arr} sub lbV ubV (Left prf)

  BT : (lt : Rel a) ->
       {arr : Array a} -> (sub : SubArray arr) ->
       (lbV, ubV : Extended a) ->
       Type
  BT lt sub lbV ubV = BT' lt sub lbV ubV (emptinessCheck sub)

------------------------------------------------------------------------
-- Safe search (with bound checking)

data View : (sub : SubArray arr) -> {b : EmptinessCheck sub} ->
            BT' lt sub lbV ubV b -> Type where
  ViewEmpty : {0 arr : Array a} -> {0 sub : SubArray arr} -> (prf : _) -> View {arr} sub (Empty prf)
  ViewNode  : {0 a : Type} -> {0 lt : Rel a} ->
              {0 arr : Array a} -> {sub : SubArray arr} ->
              {0 lbV, ubV : Extended a} ->
              (prf : LT _ _) -> (v : a) ->
              (0 val : ValueAt arr (middle sub) v) ->
              (0 lb : ExtendedLT lt lbV (Lift v)) ->
              (0 ub : ExtendedLT lt (Lift v) ubV) ->
              let cuts : (SubArray arr, SubArray arr)
                  cuts = cut sub (middleInRange prf) in
              (0 left : BT lt (fst cuts) lbV (Lift v)) ->
              (0 right : BT lt (snd cuts) (Lift v) ubV) ->
              View sub (Node prf val lb ub left right)

viewEmpty : {0 arr : Array a} -> {sub : SubArray arr} ->
            (prf : GTE _ _) -> (0 bt : BT' lt sub lbV ubV (Right prf)) -> View sub bt
viewEmpty prf (Empty _) = ViewEmpty prf

viewNode : {0 arr : Array a} -> {sub : SubArray arr} ->
           (prf : LT _ _) -> (0 bt : BT' lt sub lbV ubV (Left prf)) ->
           (v : a) -> (0 val : ValueAt arr (middle sub) v) ->
           View sub bt
viewNode prf (Node _ val' lb ub left right) v val =
  rewrite uniqueValueAt val' val in
  ViewNode prf v
    (rewrite uniqueValueAt val val' in val')
    (rewrite uniqueValueAt val val' in lb)
    (rewrite uniqueValueAt val val' in ub)
    (rewrite uniqueValueAt val val' in left)
    (rewrite uniqueValueAt val val' in right)

view : Storable a =>
       {arr : Array a} -> {sub : SubArray arr} -> {tag : EmptinessCheck sub} ->
       (0 bt : BT' lt sub lbV ubV tag) ->
       IO (View sub bt)
view {tag = Right p} bt = pure (viewEmpty p bt)
view {tag = Left p}  bt = do
    (Element v val) <- readValue sub (middle sub) (middleInRange p)
    pure (viewNode p bt v val)

search : Storable a =>
         -- looking for a needle
         (tri : (x, y : a) -> Trichotomous lt (===) (flip lt) x y) ->
         (needle : a) ->
         -- in a sorted subarray
         {arr : Array a} -> {sub : SubArray arr} -> {tag : EmptinessCheck sub} ->
         (0 bt : BT' lt sub lbV ubV tag) ->
         -- may succeed
         IO (Maybe (Subset Int (\ i => (InRange arr i, ValueAt arr i needle))))
search tri needle bt = case !(view bt) of
  ViewEmpty prf => pure Nothing
  ViewNode prf v val _ _ lft rgt =>
    case tri needle v of
      MkLT _ _ _ => search tri needle lft
      MkEQ _ p _ => pure $ Just (Element _ (inSubRange (middleInRange prf), rewrite p in val))
      MkGT _ _ _ => search tri needle rgt

{-
-- Next level:

decide : (...) -> (Dec (i : Int ** Inside lt arr lbI lbV ubI ubV i val))

Inside : (lt : a -> a -> Type) -> (arr : Array a) ->
         Int -> Extended a ->
         Int -> Extended a ->
         Int -> a -> Type
Inside lt arr lbI lbV ubI ubV i val =
  ( (lbI <= i) === True
  , (i <= ubI) === True
  , ValueAt arr i val
  , ExtendedLT lt lbV (Lift val)
  , ExtendedLT lt (Lift val) ubV
  )

-}
