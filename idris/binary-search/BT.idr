module BT

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

data View : BT' lt arr lbI lbV ubI ubV b -> Type where
  ViewEmpty : {0 lt : Rel a} -> (prf : GTE lbI ubI) -> View (Empty {lt} prf)
  ViewNode  : (prf : LT lbI ubI) -> (v : a) ->
              (0 val : ValueAt arr (middle lbI ubI) v) ->
              (0 lb : ExtendedLT lt lbV (Lift v)) ->
              (0 ub : ExtendedLT lt (Lift v) ubV) ->
              (0 left : BT lt arr lbI lbV (middle lbI ubI) (Lift v)) ->
              (0 right : BT lt arr (middle lbI ubI + 1) (Lift v) ubI ubV) ->
              View (Node prf val lb ub left right)


viewEmpty : (prf : GTE lbI ubI) -> (0 bt : BT' lt arr lbI lbV ubI ubV (Right prf)) -> View bt
viewEmpty prf (Empty _) = ViewEmpty prf

viewNode : (prf : _) -> (0 bt : BT' lt arr lbI lbV ubI ubV (Left prf)) ->
           (v : a) -> (0 val : ValueAt arr (middle lbI ubI) v) ->
           View bt
viewNode prf (Node _ val' lb ub left right) v val =
  rewrite uniqueValueAt val' val in
  ViewNode prf v
    (rewrite uniqueValueAt val val' in val')
    (rewrite uniqueValueAt val val' in lb)
    (rewrite uniqueValueAt val val' in ub)
    (rewrite uniqueValueAt val val' in left)
    (rewrite uniqueValueAt val val' in right)

view : (HasIO io, Storable a) =>
       {arr : Array a} -> {lbI, ubI : Int} ->
       {tag : Either (LT lbI ubI) (GTE lbI ubI)} ->
       (0 bt : BT' lt arr lbI lbV ubI ubV tag) ->
       io (View bt)
view {tag = Right p} bt = pure (viewEmpty p bt)
view {tag = Left p}  bt = do
    (Element v val) <- readValue arr (middle lbI ubI)
    pure (viewNode p bt v val)

search : (Storable a) =>
         -- looking for a needle
         (tri : (x, y : a) -> Trichotomous lt (===) (flip lt) x y) ->
         (needle : a) ->
         -- in a sorted array
         {arr : Array a} ->
         {lbI : Int} -> {lbV : Extended a} ->
         {ubI : Int} -> {ubV : Extended a} ->
         {tag : Either (LT lbI ubI) (GTE lbI ubI)} ->
         (0 bt : BT' lt arr lbI lbV ubI ubV tag) ->
         -- may succeed
         IO (Maybe (Subset Int (\ i => ValueAt arr i needle)))
search tri needle bt = case !(view bt) of
  ViewEmpty prf => pure Nothing
  ViewNode _ v val _ _ lft rgt => case tri needle v of
    MkLT _ _ _ => search tri needle lft
    MkEQ _ p _ => pure $ Just (Element (middle lbI ubI) (rewrite p in val))
    MkGT _ _ _ => search tri needle rgt



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
