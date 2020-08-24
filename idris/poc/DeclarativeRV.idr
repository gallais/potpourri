module DeclarativeRV

-- Not very happy with this

-- A small language with record + variant types.
-- Record & variants are declared locally using `Def` and can be
-- arbitrarily nested.

%default total

mutual
  
  data Ctx : Type where
    Epsilon : Ctx
    Comma   : (g : Ctx) -> TyDef g -> Ctx

  data TyDef : Ctx -> Type where
    Rec : List (Ty g) -> TyDef g
    Sum : List (Ty g) -> TyDef g

  data Ty : Ctx -> Type where
    Arr : Ty g -> Ty g -> Ty g
    TyC : {ty : TyDef g'} -> Elem ty g -> Ty g

  data Elem : TyDef g -> Ctx -> Type where
    Here  : Elem ty (Comma g ty)
    There : Elem ty g -> Elem ty (Comma g ty')

data DeBruijn : a -> List a -> Type where
  Z : DeBruijn a (a :: as)
  S : DeBruijn a as -> DeBruijn a (b :: as)


mutual

  weakElem : {0 ty : TyDef g'} -> Elem ty g -> Elem ty' g' -> Elem ty' g
  weakElem Here      q = There q
  weakElem (There p) q = There (weakElem p q)

  weakTy : {0 ty : TyDef g'} -> Elem ty g -> Ty g' -> Ty g
  weakTy s (Arr a b) = Arr (weakTy s a) (weakTy s b)
  weakTy s (TyC el)  = TyC (weakElem s el)

  weakTyDef : {0 ty : TyDef g'} -> Elem ty g -> TyDef g' -> TyDef g
  weakTyDef s (Rec fs) = Rec (weak s fs)
  weakTyDef s (Sum fs) = Sum (weak s fs)

  weak : {0 ty : TyDef g'} -> Elem ty g -> List (Ty g') -> List (Ty g)
  weak = map . weakTy

mutual

  -- Language with Records
  data LR : (g : Ctx) -> Ty g -> List (Ty g) -> Type where
    -- STLC
    Var : DeBruijn a as -> LR g a as
    -- 
    Lam : LR g b (a :: as) -> LR g (Arr a b) as
    Let : (0 a : Ty g) -> LR g a as -> LR g b (a :: as) -> LR g b as
    App : LR g (Arr a b) as -> LR g a as -> LR g b as
    -- Record specific functions
    Prj : (e : Elem (Rec fs) g) -> DeBruijn ty (weak e fs) -> LR g (Arr (TyC e) ty) as
    Upd : (e : Elem (Rec fs) g) -> DeBruijn ty (weak e fs) -> LR g (Arr (TyC e) (TyC e)) as
    MkR : (e : Elem (Rec fs) g) -> LRs g (weak e fs) as -> LR g (TyC e) as
    -- Variant specific functions
    Inj : (e : Elem (Sum fs) g) -> DeBruijn ty (weak e fs) -> LR g (Arr ty (TyC e)) as
    Cas : (e : Elem (Sum fs) g) -> Alts g (weak e fs) r as -> LR g (Arr (TyC e) r) as
    -- Type declaration
    Def : (d : TyDef g) -> LR (Comma g d) (weakTy Here a) (weak Here as) -> LR g a as

  data LRs : (g : Ctx) -> List (Ty g) -> List (Ty g) -> Type where
    MkU : LRs g [] as
    MkP : LR g ty as -> LRs g fs as -> LRs g (ty :: fs) as

  data Alts : (g : Ctx) -> List (Ty g) -> Ty g -> List (Ty g) -> Type where
    End : Alts g [] r as
    Alt : LR g (Arr ty r) as -> Alts g fs r as -> Alts g (ty :: fs) r as

example : {a : Ty Epsilon} -> LR Epsilon (Arr a a) []
example
  = Lam
  -- pair type
  $ Def (Rec [a, a])
  -- swap
  $ Let (Arr (TyC Here) (TyC Here))
        (Lam (MkR Here (MkP (App (Prj Here (S Z)) (Var Z))
                       (MkP (App (Prj Here Z)     (Var Z))
                        MkU))))
  -- fst $ swap $ swap (a, a)
  $ App (Prj Here Z)
  $ App (Var Z)
  $ App (Var Z)
  $ MkR Here (MkP (Var (S Z))
             (MkP (Var (S Z))
              MkU))
