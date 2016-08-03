{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE PolyKinds           #-}

module ImperativeDSL where

import GHC.TypeLits
import Data.Proxy

import NamedVariables

------------------------------------------------
-- Types
------------------------------------------------

-- Our programs are ascribed types. They are reflected
-- as real Haskell types, however we impose that they
-- should be "known" to us i.e. that we get a singleton
-- representing them.

data Type (a :: *) = KnownType a => Of

data SType (a :: *) where
  SBool :: SType Bool
  SInt  :: SType Int

instance Show (SType a) where
  show sty = case sty of
    SBool -> "Bool"
    SInt  -> "Int"

class Show a => KnownType a where sType :: Proxy a -> SType a
instance KnownType Bool where sType _ = SBool
instance KnownType Int  where sType _ = SInt

instance KnownType a => Show (Type a) where
  show Of = show $ sType (Proxy :: Proxy a)

------------------------------------------------
-- Expressions
------------------------------------------------

-- Expressions are fairly basic. We allow literals as long
-- they are of a known type.

data Exp (g :: [(Symbol,*)]) (t :: *) where
  EVar :: ScopedSymbol g s a -> Exp g a
  ELit :: KnownType s => s -> Exp g s
  EAdd :: Exp g Int -> Exp g Int -> Exp g Int
  ENot :: Exp g Bool -> Exp g Bool

instance Show (Exp g t) where
  show e = case e of
    EVar v   -> "Var " ++ show v
    ELit b   -> show b
    EAdd e f -> concat [ "(", show e, ") + (", show f, ")" ]
    ENot b   -> concat [ "¬ (", show b, ")" ]

------------------------------------------------
-- Statements
------------------------------------------------

-- A `Statement` can be seen as a Scope-transformer: it takes
-- the current scope and returns an updated one.
--   In the case of `Declare`, the returned scope has been
-- extended with the newly declared variable (and its associated
-- type).
--   In the case of `Assign`, the scope is left unchanged.

data Statement (g :: [(Symbol, *)]) (h :: [(Symbol,*)]) where
  Declare :: Name s -> Type a -> Statement g ('(s, a) ': g)
  Assign  :: ScopedSymbol g s a -> Exp g a -> Statement g g

-- `Statements` are a list of scope-aligned `Statement`s.

infixr 5 :>
data Statements (g :: [(Symbol, *)]) (h :: [(Symbol,*)]) where
  Done :: Statements g g
  (:>) :: Statement g h -> Statements h i -> Statements g i

instance Show (Statement g h) where
  show (Declare v@Var t@Of) = concat [ "new ", show v, " :: ", show t ]
  show (Assign v e)         = concat [ show v, " := ", show e ]

instance Show (Statements g h) where
  show Done         = ""
  show (st :> Done) = show st
  show (st :> rest) = concat [ show st, "\n", show rest ]

------------------------------------------------
-- Programs
------------------------------------------------

-- A Program is a sequence of `Statements` starting in the
-- empty scope.

data Program = forall h. Program (Statements '[] h)

instance Show Program where show (Program sts) = show sts
