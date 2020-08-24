module RecordAndVariants

%default total

data DeBruijn : a -> List a -> Type where
  Z : DeBruijn a (a :: as)
  S : DeBruijn a as -> DeBruijn a (b :: as)

mutual

  data NamedTys : Type where
    Empty  : NamedTys
    Extend : (f : String) -> Ty -> (fs : NamedTys) -> (0 prf : IsFresh f fs) -> NamedTys

  data IsFresh : String -> NamedTys -> Type where
    IsEmpty  : IsFresh f Empty
    IsExtend : Not (f = f') -> IsFresh f fs -> IsFresh f (Extend f' ty fs prf)

  data Ty : Type where
    Rec : NamedTys -> Ty
    Sum : NamedTys -> Ty
    Arr : Ty -> Ty -> Ty

data HasName : String -> Ty -> NamedTys -> Type where
  Here  : HasName f ty (Extend f ty fs prf)
  There : HasName f ty fs -> HasName f ty (Extend f' ty' fs prf)

mutual

  -- Language with Records
  data LR : Ty -> List Ty -> Type where
    -- STLC
    Var : DeBruijn a g -> LR a g
    Lam : LR b (a :: g) -> LR (Arr a b) g
    App : LR (Arr a b) g -> LR a g -> LR b g
    -- Record specific functions
    Prj : HasName f ty fs -> LR (Arr (Rec fs) ty) g
    Upd : HasName f ty fs -> LR (Arr (Rec fs) (Rec fs)) g
    MkR : LRs fs g -> LR (Rec fs) g 
    -- Variant specific functions
    Inj : HasName f ty fs -> LR (Arr ty (Sum fs)) g
    Cas : Alts fs r g -> LR (Arr (Sum fs) r) g

  data LRs : NamedTys -> List Ty -> Type where
    MkU : LRs Empty g
    MkP : LR ty g -> LRs fs g -> LRs (Extend f ty fs prf) g

  data Alts : NamedTys -> Ty -> List Ty -> Type where
    End : Alts Empty r g
    Alt : LR (Arr ty r) g -> Alts fs r g -> Alts (Extend f ty fs prf) r g

