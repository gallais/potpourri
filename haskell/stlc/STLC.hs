{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE PolyKinds            #-}

module STLC where

-- Defining type and the corresponding singletons

data Type = TyNat | TyBool | TyFun Type Type
data SType (t :: Type) :: * where
  STyNat  :: SType TyNat
  STyBool :: SType TyBool
  STyFun  :: SType a -> SType b -> SType (TyFun a b)

-- Contexts are lists of types

data Context = Null | Cons Context Type
data SContext (g :: Context) where
  SNull :: SContext Null
  SCons :: SContext g -> SType t -> SContext (Cons g t)

-- There is such a thing as context inclusion
-- and it is transitive

data Included (g :: Context) (h :: Context) where
  Refl :: Included g g
  Top  :: Included g h -> Included g (Cons h t)
  Pop  :: Included g h -> Included (Cons g t) (Cons h t)

trans :: Included g h -> Included h i -> Included g i
trans Refl     hi       = hi
trans gh       Refl     = gh
trans gh       (Top hi) = Top (trans gh hi)
trans (Top gh) (Pop hi) = Top (trans gh hi)
trans (Pop gh) (Pop hi) = Pop (trans gh hi)

-- Variable are fancy de Bruijn indices
-- and context inclusion induces a notion of weakening for variables

data Var (g :: Context) (n :: Type) where
  Here  :: Var (Cons g a) a
  There :: Var g a -> Var (Cons g b) a

wkVar :: Included g h -> Var g a -> Var h a
wkVar Refl      v         = v
wkVar (Top inc) v         = There $ wkVar inc v
wkVar (Pop inc) Here      = Here
wkVar (Pop inc) (There v) = There $ wkVar inc v

-- Terms can be defined in a well-scoped, well-typed fashion
-- once more inclusion induces a notion of weakening.

data Term (g :: Context) (s :: Type) where
  -- constants
  TeTrue  :: Term g TyBool
  TeFalse :: Term g TyBool
  TeZero  :: Term g TyNat
  TeSucc  :: Term g TyNat -> Term g TyNat
  -- combinators
  TeIf    :: Term g TyBool -> Term g a -> Term g a -> Term g a
  TeVar   :: Var g s -> Term g s
  TeLam   :: Term (Cons g a) b -> Term g (TyFun a b)
  TeApp   :: SType a -> Term g (TyFun a b) -> Term g a -> Term g b

wkTe :: Included g h -> Term g a -> Term h a
wkTe _   TeTrue        = TeTrue
wkTe _   TeFalse       = TeFalse
wkTe _   TeZero        = TeZero
wkTe inc (TeSucc n)    = TeSucc $ wkTe inc n
wkTe inc (TeIf b l r)  = TeIf (wkTe inc b) (wkTe inc l) (wkTe inc r)
wkTe inc (TeVar v)     = TeVar $ wkVar inc v
wkTe inc (TeApp a f t) = TeApp a (wkTe inc f) (wkTe inc t)
wkTe inc (TeLam b)     = TeLam $ wkTe (Pop inc) b

-- We now build a Kripke model for these terms by induction
-- on the type. Unsurprisingly, weakening is once more definable

type family Value (g :: Context) (t :: Type) where
  Value g TyNat       = Term g TyNat
  Value g TyBool      = Term g TyBool
  -- And now... because polymorphic types are not allowed here
  -- we use `Argh`.
  Value g (TyFun a b) = Argh g a b

newtype Argh g a b = Argh { runArgh :: forall h. SContext h -> Included g h -> Value h a -> Value h b }

wkVal :: SType s -> Included g h -> Value g s -> Value h s
wkVal STyNat       inc v = wkTe inc v
wkVal STyBool      inc v = wkTe inc v
wkVal (STyFun a b) inc v = Argh $ \ sh inc' w -> runArgh v sh (trans inc inc') w

-- The semantic counterpart of a context is an environment:
-- a list of values. Something something weakening.

data Environment (h :: Context) (g :: Context) where
  EnvNull :: Environment h Null
  EnvCons :: Environment h g -> SType t -> Value h t -> Environment h (Cons g t)

wkEnv :: Included h i -> Environment h g -> Environment i g
wkEnv _   EnvNull         = EnvNull
wkEnv inc (EnvCons e s v) = EnvCons (wkEnv inc e) s (wkVal s inc v)


-- Given a (neutral) term we can produce a value
-- and, conversely, given a value we can extract
-- a (normal) term

reflect :: SContext g -> SType s -> Term g s -> Value g s
reflect _ STyNat       t = t
reflect _ STyBool      t = t
reflect g (STyFun a b) t = Argh $ \ sh inc v -> reflect sh b (TeApp a (wkTe inc t) $ reify sh a v)

reify :: SContext g -> SType s -> Value g s -> Term g s
reify _ STyNat       v = v
reify _ STyBool      v = v
reify g (STyFun a b) v = TeLam eta
  where
    eta  = reify (SCons g a) b $ runArgh v (SCons g a) (Top Refl) zero
    zero = reflect (SCons g a) a $ TeVar Here

-- We are now ready to define the evaluation function.
-- First of all it is possible to lookup values in the environment

var :: Var g s -> Environment h g -> Value h s
var Here      (EnvCons _ _ v) = v
var (There v) (EnvCons e _ _) = var v e

-- Second, it is possible to define a semantic version of IfThenElse

valueIf :: SContext g -> SType s -> Value g TyBool -> Value g s -> Value g s -> Value g s
valueIf _ _ TeTrue  vl _  = vl
valueIf _ _ TeFalse _  vr = vr
valueIf g s ne      vl vr = reflect g s $ TeIf ne (reify g s vl) (reify g s vr)

-- Finally we can traverse the term to produce a value

eval :: SContext h -> SType s -> Term g s -> Environment h g -> Value h s
-- constants
eval _ _            TeTrue        _ = TeTrue
eval _ _            TeFalse       _ = TeFalse
eval _ _            TeZero        _ = TeZero
eval h _            (TeSucc n)    e = TeSucc $ eval h STyNat n e
-- combinators
eval h s            (TeIf b l r)  e = valueIf h s (eval h STyBool b e) (eval h s l e) (eval h s r e)
eval h s            (TeVar v)     e = var v e
eval h (STyFun a b) (TeLam body)  e = Argh $ \ sh inc v -> eval sh b body (EnvCons (wkEnv inc e) a v)
eval h b            (TeApp a f t) e = runArgh (eval h (STyFun a b) f e) h Refl $ eval h a t e

