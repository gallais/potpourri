module Record

%default total

data DeBruijn : a -> List a -> Type where
  Z : DeBruijn a (a :: as)
  S : DeBruijn a as -> DeBruijn a (b :: as)

mutual

  data RecTy : Type where
    Unit : RecTy
    Pair : (f : String) -> Ty -> (fs : RecTy) -> IsFresh f fs -> RecTy

  data IsFresh : String -> RecTy -> Type where
    FreshUnit : IsFresh f Unit
    FreshPair : Not (f = f') -> IsFresh f fs -> IsFresh f (Pair f' ty fs prf)

  data Ty : Type where
    Rec : RecTy -> Ty
    Arr : Ty -> Ty -> Ty

data IsField : String -> Ty -> RecTy -> Type where
  Here  : IsField f ty (Pair f ty fs prf)
  There : IsField f ty fs -> IsField f ty (Pair f' ty' fs prf)

mutual

  -- Language with Records
  data LR : Ty -> List Ty -> Type where
    -- STLC
    Var : DeBruijn a g -> LR a g
    Lam : LR b (a :: g) -> LR (Arr a b) g
    App : LR (Arr a b) g -> LR a g -> LR b g
    -- Record specific functions
    Prj : IsField f ty fs -> LR (Arr (Rec fs) ty) g
    MkR : LRs fs g -> LR (Rec fs) g 

  data LRs : RecTy -> List Ty -> Type where
    MkU : LRs Unit g
    MkP : LR ty g -> LRs fs g -> LRs (Pair f ty fs prf) g


