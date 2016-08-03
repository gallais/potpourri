{-# OPTIONS -Wall                   #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE StandaloneDeriving     #-}

module Semantics where

import GHC.TypeLits
import Data.Type.Equality
import NamedVariables
import ImperativeDSL


------------------------------------------------
-- Environments
------------------------------------------------

-- In order to be able to evaluate an expression, we need an
-- environment storing the values associated to each one of
-- the variables in scope.
-- Because `Declare` does not force the user to initialise
-- the variable, there may be no value whatsoever.

newtype Environment (g :: [(Symbol, *)]) =
  Environment { runEnvironment :: forall s a. Index g '(s, a) -> Maybe a }

-- We can define various combinators making it possible to
-- build up environments from old ones.

empty :: Environment '[]
empty = Environment $ \ w -> case w of {}

assign :: Environment g -> ScopedSymbol s g a -> a -> Environment g
assign rho v a = Environment $ \ w -> case indexEq (index'' v) w of
  Just Refl -> Just a
  Nothing   -> runEnvironment rho w

declare :: Environment g -> Environment ('(s, a) ': g)
declare rho = Environment $ \ v -> case v of
  Zro   -> Nothing
  Suc w -> runEnvironment rho w


------------------------------------------------
-- Evaluation
------------------------------------------------

-- If the Monad class were poly-kinded, we would require `m` to be a
-- monad.

class Eval (t :: [(Symbol, *)] -> k -> *) (m :: k -> *) | t -> m where
  eval :: t g a -> Environment g -> m a

-- Pure expressions can still fail: the type system does not ensure
-- that values have been initialised before they can be used. As a
-- consequence, we still need to define an `Error` type.

data Error where NotInitialised :: Name s -> Error
deriving instance Show Error

-- Eval for scoped symbols amounts to looking up the value in the
-- environment and raising an error if it has not been initialised.

instance Eval (ScopedSymbol s) (Either Error) where
  eval v@(The nm) rho = maybe (Left $ NotInitialised nm) Right
                      $ runEnvironment rho (index'' v)

-- Eval for expressions is a straightforward traversal where the
-- induction hypotheses are put together with the constructors'
-- semantical counterparts using applicative combinators.

instance Eval Exp (Either Error) where
  eval e rho = case e of
    EVar v   -> eval v rho
    ELit s   -> pure s
    EAdd l r -> (+) <$> eval l rho <*> eval r rho
    ENot b   -> not <$> eval b rho

-- For statements, the situation is a bit more complex: instead of
-- returning a pure value (modulo the presence of errors), one returns
-- an updated scope (modulo the presence of errors). 
-- We introduce a new type of computations and a bind-like combinator
-- making it possible to sequence statements.

newtype Computation (h :: [(Symbol, *)]) =
  Computation { runComputation :: Either Error (Environment h) }

andThen :: Computation g -> (Environment g -> Computation h) -> Computation h
andThen c f = Computation $ runComputation c >>= runComputation . f

instance Eval Statement Computation where
  eval t rho = Computation $ case t of
    Declare _ _ -> Right $ declare rho
    Assign v e  -> assign rho v <$> eval e rho

instance Eval Statements Computation where
  eval t rho = case t of
    Done      -> Computation (Right rho)
    st :> sts -> eval st rho `andThen` eval sts

-- We can finally define what it means to run a program: run the list
-- of statements using an empty environment to begin with and return
-- `()` if the evaluation is a success.

runProgram :: Program -> Either Error ()
runProgram (Program p) = () <$ runComputation (eval p empty)
