{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE MultiParamTypeClasses     #-}

module ImperativeDSL where

import GHC.TypeLits
import Data.Proxy
import Data.Type.Equality

type family If (b :: Bool) (l :: k) (r :: k) :: k where
  If 'True  l r = l
  If 'False l r = r

type family AtHead (g :: [k]) (s :: k) :: Bool where
  AtHead '[]      s = 'False
  AtHead (t ': g) s = s == t

type family HasSymbol (g :: [(Symbol,*)]) (s :: Symbol) :: Maybe * where
  HasSymbol '[]            s = 'Nothing
  HasSymbol ('(t, a) ': g) s = If (s == t) ('Just a) (HasSymbol g s)

data Index (g :: [k]) (s :: k) where
  Zro :: Index (s ': g) s
  Suc :: Index g s -> Index (t ': g) s

toInt :: Index g s -> Int
toInt Zro     = 0
toInt (Suc m) = 1 + toInt m

toEInt :: Index g s -> Exp g Int
toEInt = EInt . toInt

class HasSymbol g s ~ 'Just a => HasSymbolIdx (g :: [(Symbol,*)]) (s :: Symbol) (a :: *) (b :: Bool) where
  index :: Proxy b -> Name s -> Index g '(s, a)

instance ((s == t) ~ 'False, HasSymbolIdx g s a (AtHead g '(s, a))) => HasSymbolIdx ('(t, b) ': g) s a 'False where
  index _ nm = Suc $ index' nm

instance HasSymbolIdx ('(s, a) ': g) s a 'True where
  index _ nm = Zro

index' :: forall g s a. HasSymbolIdx g s a (AtHead g '(s, a)) => Name s -> Index g '(s, a)
index' nm = index (Proxy :: Proxy (AtHead g '(s, a))) nm

index'' :: forall g s a. ScopedSymbol g s a -> Index g '(s, a)
index'' (The nm) = index (Proxy :: Proxy (AtHead g '(s, a))) nm

test :: Exp ('("foo", Int) ': '("bar", Bool) ': '[]) Int
test = toEInt $ index' (Var :: Name "foo")

test' :: Exp ('("foo", Int) ': '("bar", Bool) ': '[]) Int
test' = toEInt $ index' (Var :: Name "bar")

test'' :: Exp ('("foo", Int) ': '("bar", Bool) ': '[]) Int
test'' = EAdd test test'

-- Renamed Proxy types for clarity
data Name (s :: Symbol) = KnownSymbol s => Var
data Type (a :: *)      = KnownType a   => Of

example' :: Statement '[] ('("foo", Int) ': '[])
example' = Declare (Var :: Name "foo") (Of :: Type Int)

data ScopedSymbol (g :: [(Symbol,*)]) (s :: Symbol) (a :: *) = forall t.
  (s ~ t, KnownSymbol s, HasSymbolIdx g s a (AtHead g '(s, a))) => The (Name t)

example :: ScopedSymbol ('("foo", Int) ': '("bar", Bool) ': '[]) "bar" Bool
example = The (Var :: Name "bar")

example'' :: Statement ('("foo", Int) ': '[]) ('("foo", Int) ': '[])
example'' = Assign (The (Var :: Name "foo")) (EInt 1)

data Statement (g :: [(Symbol, *)]) (h :: [(Symbol,*)]) where
  Declare :: Name s -> Type a -> Statement g ('(s, a) ': g)
  Assign  :: ScopedSymbol g s a -> Exp g a -> Statement g g

infixr 5 :>
data Statements (g :: [(Symbol, *)]) (h :: [(Symbol,*)]) where
  Done :: Statements g g
  (:>) :: Statement g h -> Statements h i -> Statements g i

data Program = forall h. Program (Statements '[] h)

increment :: ScopedSymbol g s Int -> Statement g g
increment v = Assign v (EAdd (EVar v) (EInt 1))

program :: Program
program = Program
  $  Declare (Var :: Name "foo") (Of :: Type Int)
  :> Assign  (The (Var :: Name "foo")) (EInt 1)
  :> Declare (Var :: Name "bar") (Of :: Type Bool)
  :> increment (The (Var :: Name "foo"))
  :> Assign  (The (Var :: Name "bar")) (ENot $ EBool True)
  :> Done

data Exp (g :: [(Symbol,*)]) (t :: *) where
  EVar    :: ScopedSymbol g s a -> Exp g a
  EBool   :: Bool -> Exp g Bool
  EInt    :: Int  -> Exp g Int
  EAdd    :: Exp g Int -> Exp g Int -> Exp g Int
  ENot    :: Exp g Bool -> Exp g Bool

instance Show (Index g s) where
  show Zro     = "Zro"
  show (Suc m) = "Suc " ++ show m

instance Show (ScopedSymbol g s a) where
  show v@(The _) = concat [ symbolVal (Proxy :: Proxy s)
                          , " (= " , show (index'' v),  ")" ]
instance Show (Exp g t) where
  show e = case e of
    EVar v   -> "Var " ++ show v
    EBool b  -> show b
    EInt i   -> show i
    EAdd e f -> concat [ "(", show e, ") + (", show f, ")" ]
    ENot b   -> concat [ "¬ (", show b, ")" ]

class KnownType a where
  display :: Type a -> String

instance KnownType Bool where
  display _ = "Bool"

instance KnownType Int where
  display _ = "Int"

instance KnownType a => Show (Type a) where
  show = display

instance KnownSymbol a => Show (Name a) where
  show _ = symbolVal (Proxy :: Proxy a)

instance Show (Statement g h) where
  show (Declare v@Var t@Of) = concat [ "new ", show v, " :: ", show t ]
  show (Assign v e)         = concat [ show v, " := ", show e ]

instance Show (Statements g h) where
  show Done         = ""
  show (st :> Done) = show st
  show (st :> rest) = concat [ show st, "\n", show rest ]

instance Show Program where
  show (Program sts) = show sts
