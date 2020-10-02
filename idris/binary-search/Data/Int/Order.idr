module Data.Int.Order

import Data.Order

%default total

-- Because we are going to essentially postulate that some equality hold
-- using `believe_me`, we better be careful about the kind of proofs we
-- trust.
public export
strictRefl : a === b -> Lazy c -> c
strictRefl Refl p = p

unsafeRefl : {0 a, b : t} -> a === b
unsafeRefl = believe_me (the (a === a) Refl)

namespace LT

  public export
  data LT : Int -> Int -> Type where
    MkLT : (a < b) === True -> LT a b

  export
  decide : (a, b : Int) -> Dec (LT a b)
  decide a b with (the (test : Bool ** (a < b) === test) (a < b ** Refl))
    decide a b | (True ** p)  = Yes (MkLT p)
    decide a b | (False ** p) = No (\ (MkLT q) => absurd (trans (sym p) q))

  export
  trans : LT a b -> LT b c -> LT a (the Int c)
  trans (MkLT p) (MkLT q)
    = strictRefl p
    $ strictRefl q
    $ MkLT unsafeRefl

  export
  irrefl : Not (LT a a)
  irrefl (MkLT p)
    = strictRefl p $ the Void
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

namespace EQ

  public export
  data EQ : Int -> Int -> Type where
    MkEQ : (a == b) === True -> EQ a b

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
  elimEQ p (MkEQ eq) v = strictRefl eq $ believe_me v

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
not_LTE_GT : Not (LTE a b) -> GT a b
not_LTE_GT p = MkLT unsafeRefl

export
inject_EQ_LTE : EQ a b -> LTE a b
inject_EQ_LTE (MkEQ p) = MkEQ p

export
inject_LT_LTE : LT a b -> LTE a b
inject_LT_LTE (MkLT p) = MkLT p

export
trans_LT_LTE : LT a b -> LTE b c -> LT a c
trans_LT_LTE p (MkLT q) = trans p (MkLT q)
trans_LT_LTE p (MkEQ q) = trans_LT_EQ p (MkEQ q)

export
trans_LTE_LT : LTE a b -> LT b c -> LT a c
trans_LTE_LT (MkLT p) q = trans (MkLT p) q
trans_LTE_LT (MkEQ p) q = trans_EQ_LT (MkEQ p) q

export
caseLTE : {0 a, b : Int} -> LTE a b -> Either (LT a b) (EQ a b)
caseLTE (MkLT p) = Left (MkLT p)
caseLTE (MkEQ p) = Right (MkEQ p)

export
trichotomous : (a, b : Int) -> Trichotomous LT EQ GT a b
trichotomous a b with (LTE.decide a b)
  trichotomous a b | Yes (MkLT p) = let lt = MkLT p in MkLT lt (LT_not_EQ lt) (LT_not_GT lt)
  trichotomous a b | Yes (MkEQ p) = let eq = MkEQ p in MkEQ (EQ_not_LT eq) eq (EQ_not_GT eq)
  trichotomous a b | No notLTE    = let gt = not_LTE_GT notLTE in MkGT (GT_not_LT gt) (GT_not_EQ gt) gt
