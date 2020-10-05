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

||| A type corresponding to a proof that a subarray is non-empty
public export
NonEmpty : SubArray arr -> Type
NonEmpty = uncurry LT . boundaries

||| A type corresponding to a check on whether a subarray is empty
public export
EmptinessCheck : SubArray arr -> Type
EmptinessCheck sub
  = Either (NonEmpty sub) (uncurry GTE (boundaries sub))

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

public export
leftSubArray : (sub : SubArray arr) -> NonEmpty sub -> SubArray arr
leftSubArray sub prf = fst (cut sub (middleInRange prf))

public export
rightSubArray : (sub : SubArray arr) -> NonEmpty sub -> SubArray arr
rightSubArray sub prf = snd (cut sub (middleInRange prf))

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
              (0 left : BT lt (leftSubArray sub prf) lbV (Lift v)) ->
              (0 right : BT lt (rightSubArray sub prf) (Lift v) ubV) ->
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

------------------------------------------------------------------------
-- Decidability proof

data Position : (sub : SubArray arr) -> NonEmpty sub -> Int -> Type where
  MkLT : InRange (leftSubArray sub prf) i -> Position sub prf i
  MkEQ : i === middle sub -> Position sub prf i
  MkGT : InRange (rightSubArray sub prf) i -> Position sub prf i

position : (sub : SubArray arr) -> (prf : NonEmpty sub) ->
           {i : Int} -> InRange sub i -> Position sub prf i
position sub prf inR = case trichotomous i (middle sub) of
  MkLT p _ _ => MkLT $ MkInterval (lowerBound inR) p
  MkEQ _ p _ => MkEQ (reflect p)
  MkGT _ _ p => MkGT $ MkInterval (suc_LT_LTE p) (upperBound inR)

bounded : (tr : {x, y, z : a} -> lt x y -> lt y z -> lt x z) ->
          {sub : SubArray arr} -> {tag : _} -> BT' lt sub lbV ubV tag ->
          {i : Int} -> InRange sub i -> {v : a} -> ValueAt arr i v ->
          (ExtendedLT lt lbV (Lift v), ExtendedLT lt (Lift v) ubV)
bounded tr (Empty prf) inR val
  = void $ irrefl $ trans_LTE_LT prf (intervalBounds inR)
bounded tr (Node prf {v = v'} val' lb ub lft rgt) inR val =
  case position sub prf inR of
    MkLT inR' => let (ih1, ih2) := bounded tr lft inR' val
                 in (ih1, trans tr ih2 ub)
    MkEQ Refl => rewrite uniqueValueAt val val' in (lb, ub)
    MkGT inR' => let (ih1, ih2) := bounded tr rgt inR' val
                 in (trans tr lb ih1, ih2)

increasing : (tr : {x, y, z : a} -> lt x y -> lt y z -> lt x z) ->
             {sub : SubArray arr} -> {tag : EmptinessCheck sub} -> BT' lt sub lbV ubV tag ->
             {i, j : Int} -> InRange sub i -> InRange sub j ->
             {v, w : _} -> ValueAt arr i v -> ValueAt arr j w ->
             LT i j -> lt v w
increasing tr (Empty prf) iinR jinR vali valj p
  = void $ irrefl $ trans_LTE_LT prf (intervalBounds iinR)
increasing tr (Node prf {v = v'} val' lb ub lft rgt) iinR jinR vali valj p =
  case (position sub prf iinR, position sub prf jinR) of
    (MkLT iinR', MkLT jinR') => increasing tr lft iinR' jinR' vali valj p
    (MkLT iinR', MkEQ Refl) =>
      rewrite uniqueValueAt valj val'
      in LiftInversion (snd (bounded tr lft iinR' vali))
    (MkLT iinR', MkGT jinR') =>
      let bndL := snd (bounded tr lft iinR' vali)
          bndR := fst (bounded tr rgt jinR' valj)
      in LiftInversion (trans tr bndL bndR)
    (MkEQ Refl, MkLT jinR') => void $ irrefl $ trans p (upperBound jinR')
    (MkEQ Refl, MkEQ Refl) => void $ irrefl p
    (MkEQ Refl, MkGT jinR') =>
      rewrite uniqueValueAt vali val'
      in LiftInversion (fst (bounded tr rgt jinR' valj))
    (MkGT iinR', MkLT jinR') => void $ irrefl $
      let 0 q : LT j (middle sub) := upperBound jinR'
          0 r : LT (middle sub) (middle sub + 1) := sucBounded (upperBound (middleInRange prf))
          0 s : LTE (middle sub + 1) i := lowerBound iinR'
      in trans p (trans q (trans_LT_LTE r s))
    (MkGT iinR', MkEQ Refl) => void $ irrefl $
      let 0 q : LT (middle sub) (middle sub + 1) := sucBounded (upperBound (middleInRange prf))
          0 r : LTE (middle sub + 1) i := lowerBound iinR'
      in trans q (trans_LTE_LT r p)
    (MkGT iinR', MkGT jinR') => increasing tr rgt iinR' jinR' vali valj p

decide' : Storable a =>
         -- looking for a needle
         (irr : {x : a} -> Not (lt x x)) ->
         (tr : {x, y, z : a} -> lt x y -> lt y z -> lt x z) ->
         (tri : (x, y : a) -> Trichotomous lt (===) (flip lt) x y) ->
         (needle : a) ->
         -- in a sorted subarray
         {arr : Array a} -> {sub : SubArray arr} -> {tag : EmptinessCheck sub} ->
         (0 bt : BT' lt sub lbV ubV tag) ->
         -- is decidable
         IO (Dec (Subset Int (\ i => (InRange sub i, ValueAt arr i needle))))
decide' irr tr tri needle bt = case !(view bt) of
  ViewEmpty prf => pure $ No \ (Element i p) =>
    void $ irrefl $ trans_LTE_LT prf (intervalBounds (fst p))
  ViewNode prf v val _ _ lft rgt =>
    case tri needle v of
      MkLT p _ _ => case !(decide' irr tr tri needle lft) of
        Yes (Element i q) => do
          let 0 inR : InRange sub i
              := expandIntervalRight (fst q) (inject_LT_LTE (upperBound (middleInRange prf)))
          pure $ Yes (Element i (inR, snd q))
        No contra => pure $ No $ \ (Element i q) => void $ case position sub prf (fst q) of
          MkLT inR => contra (Element i (inR, snd q)) -- TODO
          MkEQ Refl => irr (replace {p = lt needle} (uniqueValueAt val (snd q)) p)
          MkGT inR =>
            let r : lt v needle := LiftInversion (fst (bounded tr rgt inR (snd q)))
            in irr (tr p r)
      MkEQ _ p _ => pure $ Yes (Element _ (middleInRange prf, rewrite p in val))
      MkGT _ _ p => case !(decide' irr tr tri needle rgt) of
        Yes (Element i p) => do
          let 0 lte : LTE (fst (begin sub)) (middle sub + 1)
                    := let (MkInterval p q) := middleInRange prf in trans p (inject_LT_LTE (sucBounded q))
              0 inR : InRange sub i
              := expandIntervalLeft lte (fst p)
          pure $ Yes (Element i (inR, snd p))
        No contra => pure $ No $ \ (Element i q) => void $ case position sub prf (fst q) of
          MkLT inR =>
            let r : lt needle v := LiftInversion (snd (bounded tr lft inR (snd q)))
            in irr (tr p r)
          MkEQ Refl => irr (replace {p = lt v} (uniqueValueAt (snd q) val) p)
          MkGT inR => contra (Element i (inR, snd q))


decide : Storable a =>
         -- provided the order has good properties
         (irr : {x : a} -> Not (lt x x)) ->
         (tr : {x, y, z : a} -> lt x y -> lt y z -> lt x z) ->
         (tri : (x, y : a) -> Trichotomous lt (===) (flip lt) x y) ->
         -- looking a needle up
         (needle : a) ->
         -- in a sorted array
         (arr : Array a) -> (0 bt : BT lt (whole arr) lbV ubV) ->
         -- is decidable
         IO (Dec (Subset Int (\ i => (InRange arr i, ValueAt arr i needle))))
decide irr tr tri needle arr bt = decide' irr tr tri needle bt
