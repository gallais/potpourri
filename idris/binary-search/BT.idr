module BT

import Data.Buffer
import Data.Nat
import Data.DPair
import Data.Array.ReadOnly

%default total

data Extended a = MInf | PInf | Lift a

data ExtendedLT : (a -> a -> Type) -> (Extended a -> Extended a -> Type) where
  MInfPInf : ExtendedLT lt MInf PInf
  MInfLift : ExtendedLT lt MInf (Lift v)
  LiftLift : {0 v, w : a} -> lt v w -> ExtendedLT lt (Lift v) (Lift w)
  LiftPInf : ExtendedLT lt (Lift v) PInf


-- ||| The inductive type `BT lt arr lbI lbV ubI ubV` is a proof that between
-- ||| the indices `lbI` and `ubI` the array `arr` is sorted containing values
-- ||| bounded by `lbV` and `ubV`.
-- ||| The proof takes the form of a binary search tree which should allow us
-- ||| to efficiently explore the array in an obviously terminating way!

data BT' : {0 a : Type} ->
           (lt : a -> a -> Type) ->                -- strict order
           (arr : Array a) ->                      -- array of data
           (lbI : Int) -> (lbV : Extended a) ->    -- lower index & value
           (ubI : Int) -> (ubV : Extended a) ->    -- upper index & value
           (tag : Bool) ->                         -- `lbI > ubI`?
           Type where
  Empty : {0 a : Type} -> {0 lt : a -> a -> Type} -> {0 arr : Array a} ->
          {0 lbI, ubI : Int} -> {0 lbV, ubV : Extended a} ->
          BT' {a} lt arr lbI lbV ubI ubV True
  Node  : {0 a : Type} -> {0 lt : a -> a -> Type} -> {0 arr : Array a} ->
          {0 lbI, ubI : Int} -> {0 lbV, ubV : Extended a} ->
          let index = middle lbI ubI in
          {0 v : a} -> ValueAt arr index v ->
          ExtendedLT lt lbV (Lift v) -> ExtendedLT lt (Lift v) ubV ->
          BT' lt arr lbI lbV (index - 1) (Lift v) (lbI > index - 1) ->
          BT' lt arr (index + 1) (Lift v) ubI ubV (index + 1 > ubI) ->
          BT' lt arr lbI lbV ubI ubV False

BT : (lt : a -> a -> Type) ->
     (arr : Array a) ->
     (lbI : Int) -> (lbV : Extended a) ->
     (ubI : Int) -> (ubV : Extended a) ->
     Type
BT lt arr lbI lbV ubI ubV = BT' lt arr lbI lbV ubI ubV (lbI > ubI)

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

data View : BT' lt arr lbI lbV ubI ubV b -> Type where
  ViewEmpty : View Empty
  ViewNode  : {0 lt : a -> a -> Type} -> {0 arr : Array a} ->
              {0 lbI, ubI : Int} -> {0 lbV, ubV : Extended a} ->
              (v : a) ->
              let 0 index : Int; index = middle lbI ubI in
              (0 prf : ValueAt arr index v) ->
              (0 lb : ExtendedLT lt lbV (Lift v)) ->
              (0 ub : ExtendedLT lt (Lift v) ubV) ->
              (0 left : BT lt arr lbI lbV (index - 1) (Lift v)) ->
              (0 right : BT lt arr (index + 1) (Lift v) ubI ubV) ->
              View (Node prf lb ub left right)

viewEmpty : (0 bt : BT' lt arr lbI lbV ubI ubV True) -> View bt
viewEmpty Empty = ViewEmpty

viewNode : (0 bt : BT' lt arr lbI lbV ubI ubV False) ->
           (v : a) -> (0 prf : ValueAt arr (middle lbI ubI) v) ->
           View bt
viewNode (Node prf' lb ub left right) v prf =
  rewrite uniqueValueAt prf' prf in
  ViewNode v
    (rewrite uniqueValueAt prf prf' in prf')
    (rewrite uniqueValueAt prf prf' in lb)
    (rewrite uniqueValueAt prf prf' in ub)
    (rewrite uniqueValueAt prf prf' in left)
    (rewrite uniqueValueAt prf prf' in right)

view : (HasIO io, Storable a) =>
       (arr : Array a) -> (lbI, ubI : Int) ->
       (0 bt : BT lt arr lbI lbV ubI ubV) -> io (View bt)
view arr lbI ubI bt with (lbI > ubI)
  view arr lbI ubI bt | True = pure (viewEmpty bt)
  view arr lbI ubI bt | False = do
    (Element v prf) <- readValue arr (middle lbI ubI) ?prf
    pure (viewNode bt v prf)

data Trichotomy : (eq, lt : a -> a -> Type) -> (a -> a -> Type) where
  LT : {0 x, y : a} -> lt x y -> Trichotomy eq lt x y
  EQ : {0 x, y : a} -> eq x y -> Trichotomy eq lt x x
  GT : {0 x, y : a} -> lt y x -> Trichotomy eq lt x y

interface Trichotomous (a : Type) (eq, lt : a -> a -> Type) where

  trichotomy' : (x, y : a) -> Trichotomy eq lt x y

trichotomy : (0 lt : a -> a -> Type) -> Trichotomous a (===) lt =>
             (x, y : a) -> Trichotomy (===) lt x y
trichotomy lt = trichotomy' {lt}

search : (Storable a, Trichotomous a (===) lt) =>
         (arr : Array a) ->
         (lbI : Int) -> (lbV : Extended a) ->
         (ubI : Int) -> (ubV : Extended a) ->
         (0 bt : BT' lt arr lbI lbV ubI ubV (lbI > ubI)) ->
         (val : a) ->
         IO (Dec (i : Int ** Inside lt arr lbI lbV ubI ubV i val))
search arr lbI lbV ubI ubV bt val with (the (IO _) (view arr lbI ubI bt))
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
