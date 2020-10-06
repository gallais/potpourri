module Data.Int.Order

import Data.Order

%default total

------------------------------------------------------------------------
-- Prelude

-- Because we are going to essentially postulate that some equality hold
-- using `believe_me`, we better be careful about the kind of proofs we
-- trust.
export
strictRefl : a === b -> Lazy c -> c
strictRefl Refl p = p

-- Do NOT re-export
unsafeRefl : {0 a, b : t} -> a === b
unsafeRefl = believe_me (the (a === a) Refl)

------------------------------------------------------------------------
-- LT

namespace LT

  public export
  data LT : Int -> Int -> Type where
    MkLT : (a < b) === True -> LT a b

  export
  strictLT : LT a b -> Lazy c -> c
  strictLT (MkLT p) c = strictRefl p c

  export
  decide : (a, b : Int) -> Dec (LT a b)
  decide a b with (the (test : Bool ** (a < b) === test) (a < b ** Refl))
    decide a b | (True ** p)  = Yes (MkLT p)
    decide a b | (False ** p) = No (\ (MkLT q) => absurd (trans (sym p) q))

  export
  trans : LT a b -> LT b c -> LT a (the Int c)
  trans p q = strictLT p $ strictLT q $ MkLT unsafeRefl

  export
  irrefl : Not (LT a a)
  irrefl p = strictLT p $ the Void
           $ assert_total $ idris_crash "IMPOSSIBLE: LT is irreflexive"

public export
GT : Int -> Int -> Type
GT = flip LT

export
LT_not_GT : LT a b -> Not (GT a b)
LT_not_GT p q = irrefl (trans p q)

export
GT_not_LT : GT a b -> Not (LT a b)
GT_not_LT = flip LT_not_GT

------------------------------------------------------------------------
-- EQ

namespace EQ

  public export
  data EQ : Int -> Int -> Type where
    MkEQ : (a == b) === True -> EQ a b

  export
  strictEQ : EQ a b -> Lazy c -> c
  strictEQ (MkEQ p) c = strictRefl p c

  export
  decide : (a, b : Int) -> Dec (EQ a b)
  decide a b with (the (test : Bool ** (a == b) === test) (a == b ** Refl))
    decide a b | (True  ** p) = Yes (MkEQ p)
    decide a b | (False ** p) = No (\ (MkEQ q) => absurd (trans (sym p) q))

  export
  refl : EQ a a
  refl = MkEQ unsafeRefl

  export
  elimEQ : (0 p : Int -> Type) -> EQ a b -> p a -> p b
  elimEQ _ p v = strictEQ p $ believe_me v

  export
  reflect : EQ a b -> a === b
  reflect p = elimEQ (\ b => a === b) p Refl

  export
  sym : EQ a b -> EQ b a
  sym p = elimEQ (\ b => EQ b a) p refl

  export
  trans : EQ a b -> EQ b c -> EQ a c
  trans p q = elimEQ (\ b => EQ b c) (sym p) q

export
trans_LT_EQ : LT a b -> EQ b c -> LT a c
trans_LT_EQ p q = elimEQ (LT a) q p

export
trans_EQ_LT : EQ a b -> LT b c -> LT a c
trans_EQ_LT p q = elimEQ (\ b => LT b c) (sym p) q

export
LT_not_EQ : LT a b -> Not (EQ a b)
LT_not_EQ p q = irrefl (trans_LT_EQ p (sym q))

export
EQ_not_LT : EQ a b -> Not (LT a b)
EQ_not_LT = flip LT_not_EQ

export
EQ_not_GT : EQ a b -> Not (GT a b)
EQ_not_GT = EQ_not_LT . sym

export
GT_not_EQ : GT a b -> Not (EQ a b)
GT_not_EQ = flip EQ_not_GT

------------------------------------------------------------------------
-- LTE

namespace LTE

  public export
  data LTE : Int -> Int -> Type where
    MkLT : (a < b)  === True -> LTE a b
    MkEQ : (a == b) === True -> LTE a b

  export
  decide : (a, b : Int) -> Dec (LTE a b)
  decide a b with (LT.decide a b)
    decide a b | Yes (MkLT p) = Yes (MkLT p)
    decide a b | No notLT with (EQ.decide a b)
      decide a b | No notLT | Yes (MkEQ p) = Yes (MkEQ p)
      decide a b | No notLT | No notEQ = No $ \ case
        MkLT p => notLT (MkLT p)
        MkEQ p => notEQ (MkEQ p)

  export
  refl : LTE a a
  refl = MkEQ unsafeRefl

  export
  trans_LT_LTE : LT a b -> LTE b c -> LT a c
  trans_LT_LTE p (MkLT q) = trans p (MkLT q)
  trans_LT_LTE p (MkEQ q) = trans_LT_EQ p (MkEQ q)

  export
  trans_LTE_LT : LTE a b -> LT b c -> LT a c
  trans_LTE_LT (MkLT p) q = trans (MkLT p) q
  trans_LTE_LT (MkEQ p) q = trans_EQ_LT (MkEQ p) q

  export
  inject_LT_LTE : LT a b -> LTE a b
  inject_LT_LTE (MkLT p) = MkLT p

  export
  inject_EQ_LTE : EQ a b -> LTE a b
  inject_EQ_LTE (MkEQ p) = MkEQ p

  export
  trans : LTE a b -> LTE b c -> LTE a c
  trans (MkLT p) q = inject_LT_LTE (trans_LT_LTE (MkLT p) q)
  trans p (MkLT q) = inject_LT_LTE (trans_LTE_LT p (MkLT q))
  trans (MkEQ p) (MkEQ q) = inject_EQ_LTE (trans (MkEQ p) (MkEQ q))

export
strictLTE : LTE a b -> Lazy c -> c
strictLTE (MkLT p) q = strictRefl p q
strictLTE (MkEQ p) q = strictRefl p q

public export
GTE : Int -> Int -> Type
GTE = flip LTE

export
caseLTE : LTE a b -> Either (LT a b) (EQ a b)
caseLTE (MkLT p) = Left (MkLT p)
caseLTE (MkEQ p) = Right (MkEQ p)

------------------------------------------------------------------------
-- Trichotomy and other decidability results

export
trichotomous : (a, b : Int) -> Trichotomous LT EQ GT a b
trichotomous a b with (LTE.decide a b)
  trichotomous a b | Yes (MkLT p) = let lt = MkLT p in MkLT lt (LT_not_EQ lt) (LT_not_GT lt)
  trichotomous a b | Yes (MkEQ p) = let eq = MkEQ p in MkEQ (EQ_not_LT eq) eq (EQ_not_GT eq)
  trichotomous a b | No notLTE    = let gt = MkLT unsafeRefl in MkGT (GT_not_LT gt) (GT_not_EQ gt) gt

export
decide_LT_GTE : (a, b : Int) -> Either (LT a b) (GTE a b)
decide_LT_GTE a b with (trichotomous a b)
  decide_LT_GTE a b | MkLT lt _ _ = Left lt
  decide_LT_GTE a b | MkEQ _ eq _ = Right (inject_EQ_LTE (sym eq))
  decide_LT_GTE a b | MkGT _ _ gt = Right (inject_LT_LTE gt)

------------------------------------------------------------------------
-- Some properties

export
suc_LT_LTE : {a, b : Int} -> LT a b -> LTE (a + 1) b
suc_LT_LTE p with (the (test : Bool ** (a + 1 == b) === test) (a + 1 == b ** Refl))
  suc_LT_LTE p | (True  ** q) = MkEQ q
  suc_LT_LTE p | (False ** _) = MkLT unsafeRefl

export
sucBounded : LT a b -> LT a (a + 1)
sucBounded p = strictLT p $ MkLT unsafeRefl

export
pred_LT_LTE : {a, b : Int} -> LT a b -> LTE a (b - 1)
pred_LT_LTE p with (the (test : Bool ** (a == b - 1) === test) (a == b - 1 ** Refl))
  pred_LT_LTE p | (True  ** q) = MkEQ q
  pred_LT_LTE p | (False ** _) = MkLT unsafeRefl

------------------------------------------------------------------------
-- Intervals

||| And interval is an `Int -> Type` predicate characterised by 4 parameters:
||| @lbI for whether the lower bound is inclusive
||| @ubI for whether the upper bound is inclusive
||| @lb  for the lower bound
||| @ub  for the upper bound
||| @i   is the integer being talked about
public export
record Interval (lbI, ubI : Bool) (lb, ub : Int) (i : Int) where
  constructor MkInterval
  lowerBound : (ifThenElse lbI LTE LT) lb i
  upperBound : (ifThenElse ubI LTE LT) i ub

namespace Interval

  export
  decide : {lbI, ubI : Bool} -> (lb, ub, i : Int) -> Dec (Interval lbI ubI lb ub i)
  decide lb ub i = case decide lbI lb i of
    No contra => No (contra . lowerBound)
    Yes p => case decide ubI i ub of
      No contra => No (contra . upperBound)
      Yes q => Yes (MkInterval p q)

    where

      decide : (b : Bool) -> (v, w : Int) -> Dec (ifThenElse b LTE LT v w)
      decide True = LTE.decide
      decide False = LT.decide

||| If an interval is non-empty then we can conclude that the lower bound is less
||| than (or equal to potentially) the upper bound
export
intervalBounds : {lbI, ubI : Bool} -> Interval lbI ubI lb ub i ->
                 ifThenElse (lbI && ubI) LTE LT lb ub
intervalBounds {lbI = True} {ubI = True} i = LTE.trans (lowerBound i) (upperBound i)
intervalBounds {lbI = False} {ubI = True} i = trans_LT_LTE (lowerBound i) (upperBound i)
intervalBounds {lbI = True} {ubI = False} i = trans_LTE_LT (lowerBound i) (upperBound i)
intervalBounds {lbI = False} {ubI = False} i = trans (lowerBound i) (upperBound i)

export
expandIntervalLeft : {lbI : Bool} -> LTE a lb -> Interval lbI ubI lb ub i -> Interval lbI ubI a ub i
expandIntervalLeft {lbI = True} p (MkInterval isLB isUB) = MkInterval (trans p isLB) isUB
expandIntervalLeft {lbI = False} p (MkInterval isLB isUB) = MkInterval (trans_LTE_LT p isLB) isUB

export
expandIntervalRight : {ubI : Bool} -> Interval lbI ubI lb ub i -> LTE ub a -> Interval lbI ubI lb a i
expandIntervalRight {ubI = True} (MkInterval isLB isUB) p = MkInterval isLB (trans isUB p)
expandIntervalRight {ubI = False} (MkInterval isLB isUB) p = MkInterval isLB (trans_LT_LTE isUB p)

public export
ClosedInterval : (lb, ub : Int) -> (Int -> Type)
ClosedInterval = Interval True True

export
inClosedInterval : {lbI, ubI : Bool} -> Interval lbI ubI lb ub i -> ClosedInterval lb ub i
inClosedInterval (MkInterval isLB isUB) = MkInterval (relax _ isLB) (relax _ isUB) where

  relax : (b : Bool) -> ifThenElse b LTE LT v w -> LTE v w
  relax True p = p
  relax False p = inject_LT_LTE p

export
sucInterval : {i, ub : Int} -> Interval True False lb ub i -> Interval False True lb ub (i + 1)
sucInterval (MkInterval isLB isUB)
  = MkInterval (strictLTE isLB (MkLT unsafeRefl)) (suc_LT_LTE isUB)

export
lbInClosedInterval : LTE lb ub -> ClosedInterval lb ub lb
lbInClosedInterval = MkInterval refl

export
ubInClosedInterval : LTE lb ub -> ClosedInterval lb ub ub
ubInClosedInterval p = MkInterval p refl

public export
OpenInterval : (lb, ub : Int) -> (Int -> Type)
OpenInterval = Interval False False

------------------------------------------------------------------------
-- Middle point

||| Provided that `LTE a b`, the computation of middle should not overflow
public export
middle : (a, b : Int) -> Int
middle a b = a + ((b - a) `shiftR` 1)

||| Provided that `LT a b`, we can guarantee that `middle a b` is in [|a,b[|.
export
middleInInterval : {a, b : Int} -> LT a b -> Interval True False a b (middle a b)
middleInInterval p = strictLT p $ MkInterval unsafeLTE (MkLT unsafeRefl)

  where

    ||| DO NOT re-export!
    unsafeLTE : LTE a (middle a b)
    unsafeLTE with (LTE.decide a (middle a b))
    unsafeLTE | Yes p = p
    unsafeLTE | No np = assert_total $ idris_crash "Error: invalid call to unsafeLTE"
