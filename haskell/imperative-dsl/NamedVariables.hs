{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE StandaloneDeriving    #-}

module NamedVariables where

import GHC.TypeLits
import Data.Proxy
import Data.Type.Equality

------------------------------------------------
-- Well-Typed and Well-Scoped De Bruijn indices
------------------------------------------------

data Index (g :: [k]) (s :: k) where
  Zro :: Index (s ': g) s
  Suc :: Index g s -> Index (t ': g) s
deriving instance Show (Index g s)

toInt :: Index g s -> Int
toInt Zro     = 0
toInt (Suc m) = 1 + toInt m

-- Given a named variable, lookup the associated type in the
-- context, fail if it is not in scope.
type family If (b :: Bool) (l :: k) (r :: k) :: k where
  If 'True  l r = l
  If 'False l r = r

-- Using `If` rather than a syntactic equality test means that
-- if we have a constrating `(s == t) ~ 'False` in context then
-- `HasSymbol ('(t, a) ': g) s` *will* reduce to `HasSymbol g s`.
type family HasSymbol (g :: [(Symbol,*)]) (s :: Symbol) :: Maybe * where
  HasSymbol '[]            s = 'Nothing
  HasSymbol ('(t, a) ': g) s = If (s == t) ('Just a) (HasSymbol g s)

------------------------------------------------
-- Named Variables
------------------------------------------------

-- We don't want our users to use raw de Bruijn index so we
-- provide them with a proxy type called `Name` making it
-- possible to mention type-level variable names.
data Name (s :: Symbol) = KnownSymbol s => Var

-- The `KnownSymbol` constraint on the constructor `Var` makes
-- it possible to `Show` a `Name`:
instance Show (Name a) where
  show Var = symbolVal (Proxy :: Proxy a)

-- `ScopedSymbol` is a way to state that a named variable
-- is indeed in Scope and has a given type.
data ScopedSymbol (g :: [(Symbol,*)]) (s :: Symbol) (a :: *) =
  (HasSymbolIdx g s a (AtHead g '(s, a))) => The (Name s)

instance Show (ScopedSymbol g s a) where
  show v@(The nm) = concat [ show nm, " (= " , show (index'' v),  ")" ]

------------------------------------------------
-- Reification of variables in Scope
------------------------------------------------

-- To each variable in Scope we can programmatically associate
-- a corresponding de Bruijn index.

-- In order to avoid having overlapping instances, `HasSymbol`
-- will take an extra `Bool` parameter guiding the search. In
-- practice this boolean will always be the result of calling
-- `AtHead`: the instance is picked depending on whether we
-- just found the variable we are looking for sitting at the
-- top of the context.

type family AtHead (g :: [k]) (s :: k) :: Bool where
  AtHead '[]      s = 'False
  AtHead (t ': g) s = s == t

class HasSymbol g s ~ 'Just a =>
      HasSymbolIdx (g :: [(Symbol,*)]) (s :: Symbol) (a :: *) (b :: Bool) where
  index :: Proxy b -> Name s -> Index g '(s, a)

instance HasSymbolIdx ('(s, a) ': g) s a 'True where
  index _ nm = Zro

instance ((s == t) ~ 'False, HasSymbolIdx g s a (AtHead g '(s, a))) =>
         HasSymbolIdx ('(t, b) ': g) s a 'False where
  index _ nm = Suc $ index' nm

-- Specialised versions of `index` instantiating the `Proxy` to
-- what it should be.
index' :: forall g s a. HasSymbolIdx g s a (AtHead g '(s, a)) => Name s -> Index g '(s, a)
index' nm = index (Proxy :: Proxy (AtHead g '(s, a))) nm

index'' :: forall g s a. ScopedSymbol g s a -> Index g '(s, a)
index'' (The nm) = index (Proxy :: Proxy (AtHead g '(s, a))) nm
