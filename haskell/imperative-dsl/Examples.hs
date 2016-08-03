{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Examples where

import NamedVariables
import ImperativeDSL

toExp :: Index g s -> Exp g Int
toExp = ELit . toInt

-- Looking up various variables' index to check that
-- HasSymbolIdx works correctly
foosIndex :: Exp ('("foo", Int) ': '("bar", Bool) ': '[]) Int
foosIndex = toExp $ index' (Var :: Name "foo")

barsIndex :: Exp ('("foo", Int) ': '("bar", Bool) ': '[]) Int
barsIndex = toExp $ index' (Var :: Name "bar")

-- One of the advantages of EDSLs is that we inherit the ability
-- to have auxiliary definitions from the host language. Here
-- we add the two indexes computed previously.
addIndexes :: Exp ('("foo", Int) ': '("bar", Bool) ': '[]) Int
addIndexes = EAdd foosIndex barsIndex

-- Showing of the ability to mention a variable by name and get
-- its type right
theVarBar :: ScopedSymbol "bar" ('("foo", Int) ': '("bar", Bool) ': '[]) Bool
theVarBar = The (Var :: Name "bar")

-- Small demonstration of Name & Type vs. ScopedSymbol
declareFoo :: Statement g ('("foo", Int) ': g)
declareFoo = Declare (Var :: Name "foo") (Of :: Type Int)

assignFoo :: Statement ('("foo", Int) ': '[]) ('("foo", Int) ': '[])
assignFoo = Assign (The (Var :: Name "foo")) (ELit 1)

-- Another advantage of EDSLs: the ability to use the host
-- language's abstraction mechanism to define parametrised
-- procedures.
increment :: ScopedSymbol s g Int -> Statement g g
increment v = Assign v (EAdd (EVar v) (ELit 1))

-- Example program using previously declared subprograms
-- as well as raw definitions showing that typechecking
-- works just fine even without annotations for each one
-- of the statements.
program :: Program
program = Program
  $  declareFoo
  :> assignFoo
  :> Declare (Var :: Name "bar") (Of :: Type Bool)
  :> increment (The (Var :: Name "foo"))
  :> Assign  (The (Var :: Name "bar")) (ENot $ ELit True)
  :> Done
