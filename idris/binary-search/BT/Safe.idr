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

mutual

  ||| The inductive type `BT'` proves that a given subarray is sorted.
  ||| @lt  is the strict ordering used for this notion of being sorted
  ||| @arr is the underlying physical (read-only) array
  ||| The subarray is contained between two bounds:
  ||| @lbI is the (inclusive) lower bound
  ||| @ubI is the (exclusive) upper bound
  ||| And the values in the subarray thus delimited are contained between two
  ||| (exclusive) bounds:
  ||| @lbV is the lower bound
  ||| @ubV is the upper bound
  ||| Finally, a tag:
  ||| @tag helps Idris see that the two constructors are disjoint

  data BT' : (lt : Rel a) ->
             (arr : Array a) ->
             (lbI : Int) -> (lbV : Extended a) ->
             (ubI : Int) -> (ubV : Extended a) ->
             (tag : Either (LT lbI ubI) (GTE lbI ubI)) ->
             Type where
    ||| If the range [lbI..ubI] is empty then the proof is trivial
    Empty : (prf : GTE lbI ubI) -> BT' lt arr lbI lbV ubI ubV (Right prf)

    ||| Otherwise the expect the value at position `middle lbI ubI`
    ||| to be bounded by `lbV` and `ubV` and the subarrays to the
    ||| left and to the right of this middle point to be sorted too.
    Node  : (prf : LT lbI ubI) ->
            -- value in the middle position
            ValueAt arr (middle lbI ubI) v ->
            ExtendedLT lt lbV (Lift v) -> ExtendedLT lt (Lift v) ubV ->
            -- each half is sorted too
            BT lt arr lbI lbV (middle lbI ubI) (Lift v) ->
            BT lt arr (middle lbI ubI + 1) (Lift v) ubI ubV ->
            -- whole subarray is sorted
            BT' lt arr lbI lbV ubI ubV (Left prf)

  BT : (lt : Rel a) ->
       (arr : Array a) ->
       (lbI : Int) -> (lbV : Extended a) ->
       (ubI : Int) -> (ubV : Extended a) ->
       Type
  BT lt arr lbI lbV ubI ubV = BT' lt arr lbI lbV ubI ubV (decide_LT_GTE lbI ubI)

------------------------------------------------------------------------
-- Safe search (with bound checking)

public export
EmptinessCheck : SubArray arr -> Type
EmptinessCheck sub =
  let bnds : (Int, Int); bnds = boundaries sub
      start : Int; start = fst bnds
      finish : Int; finish = snd bnds
  in Either (LT start finish) (GTE start finish)

public export
SUB' : (lt : a -> a -> Type) -> {arr : Array a} -> (sub : SubArray arr) ->
       (lbV, ubV : Extended a) -> (tag : EmptinessCheck sub) ->
       Type
SUB' lt sub lbV ubV tag =
  let bnds : (Int, Int); bnds = boundaries sub
      start : Int; start = fst bnds
      finish : Int; finish = snd bnds
  in BT' lt arr start lbV finish ubV tag

public export
SUB : (lt : a -> a -> Type) -> {arr : Array a} -> (sub : SubArray arr) ->
      (lbV, ubV : Extended a) -> Type
SUB lt sub lbV ubV = SUB' lt sub lbV ubV (decide_LT_GTE _ _)

data View : (sub : SubArray arr) -> {b : EmptinessCheck sub} ->
            SUB' lt sub lbV ubV b -> Type where
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
              (0 left : SUB lt (fst cuts) lbV (Lift v)) ->
              (0 right : SUB lt (snd cuts) (Lift v) ubV) ->
              View sub (Node prf val lb ub left right)

viewEmpty : {0 arr : Array a} -> {sub : SubArray arr} ->
            (prf : GTE _ _) -> (0 bt : SUB' lt sub lbV ubV (Right prf)) -> View sub bt
viewEmpty prf (Empty _) = ViewEmpty prf

viewNode : {0 arr : Array a} -> {sub : SubArray arr} ->
           (prf : LT _ _) -> (0 bt : SUB' lt sub lbV ubV (Left prf)) ->
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

view : {0 a : Type} -> {0 lt : a -> a -> Type} -> (Storable a) =>
       {arr : Array a} -> (sub : SubArray arr) -> {tag : EmptinessCheck sub} ->
       {0 lbV, ubV : Extended a} ->
       (0 bt : SUB' lt sub lbV ubV tag) ->
       IO (View sub bt)
view {tag = Right p} sub bt = pure (viewEmpty p bt)
view {tag = Left p}  sub bt = do
    (Element v val) <- readValue sub (middle sub) (middleInRange p)
    pure (viewNode p bt v val)

search : {0 a : Type} -> {0 lt : a -> a -> Type} -> (Storable a) =>
         -- looking for a needle
         (tri : (x, y : a) -> Trichotomous lt (===) (flip lt) x y) ->
         (needle : a) ->
         -- in a sorted subarray
         {arr : Array a} -> (sub : SubArray arr) -> {tag : EmptinessCheck sub} ->
         {lbV, ubV : Extended a} ->
         (0 bt : SUB' lt sub lbV ubV tag) ->
         -- may succeed
         IO (Maybe (Subset Int (\ i => ValueAt arr i needle)))
search tri needle sub bt = case !(view sub bt) of
  ViewEmpty prf => pure Nothing
  ViewNode prf v val _ _ lft rgt =>
    let cuts : (SubArray arr, SubArray arr); cuts = cut sub (middleInRange prf) in
    case tri needle v of
      MkLT _ _ _ => search tri needle (fst cuts) lft
      MkEQ _ p _ => pure $ Just (Element _ (rewrite p in val))
      MkGT _ _ _ => search tri needle (snd cuts) rgt

{-
with (the (IO _) (view arr lbI ubI bt))
  search arr lbI lbV ubI ubV bt val | tag with (lbI > ubI)
    search arr lbI lbV ubI ubV bt val | tag | b = do
      let index : Int
          index = middle lbI ubI
      case !tag of
        ViewEmpty => pure (No ?contra)
        ViewNode v prf lb ub left right => case trichotomy lt v val of
          LT lt => ?a
          EQ eq => pure $ Yes (index ** ?hole)
          GT gt => ?b
-}


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
