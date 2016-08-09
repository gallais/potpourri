{-# OPTIONS -Wall                   #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE StandaloneDeriving     #-}

module Semantics where

import GHC.Prim
import GHC.TypeLits
import Data.Type.Equality
import NamedVariables
import ImperativeDSL

import Control.Monad.Except
import Control.Monad.Writer

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

class Eval (t :: [(Symbol, *)] -> k -> *) (m :: * -> *) where
  type Result t (a :: k)
  type Constr t m :: Constraint
  eval :: (Monad m, Constr t m) => t g a -> Environment g -> m (Result t a)


-- Pure expressions can still fail: the type system does not ensure
-- that values have been initialised before they can be used. As a
-- consequence, we still need to define an `Error` type.

data Error where NotInitialised :: Name s -> Error
deriving instance Show Error

-- Eval for scoped symbols amounts to looking up the value in the
-- environment and raising an error if it has not been initialised.

instance Eval (ScopedSymbol s) m where
  type Result (ScopedSymbol s) a = a
  type Constr (ScopedSymbol s) m = MonadError Error m
  eval v@(The nm) rho = maybe (throwError $ NotInitialised nm) pure
                      $ runEnvironment rho (index'' v)

-- Eval for expressions is a straightforward traversal where the
-- induction hypotheses are put together with the constructors'
-- semantical counterparts using applicative combinators.

instance Eval Exp m where
  type Result Exp a = a
  type Constr Exp m = MonadError Error m
  eval e rho = case e of
    EVar v   -> eval v rho
    ELit s   -> pure s
    EAdd l r -> (+) <$> eval l rho <*> eval r rho
    ENot b   -> not <$> eval b rho

-- Statements are scope-transformer. As such, their evaluation
-- yields not a value but a new environment corresponding to the
-- modified scope.

instance Eval Statement m where
  type Result Statement h = Environment h
  type Constr Statement m = (MonadError Error m, MonadWriter String m)
  eval t rho = case t of
    Declare _ _ -> pure $ declare rho
    Assign v e  -> assign rho v <$> eval e rho
    Print e     -> rho <$ (eval e rho >>= tell . show)

instance Eval Statements m where
  type Result Statements h = Environment h
  type Constr Statements m = (MonadError Error m, MonadWriter String m)
  eval t rho = case t of
    Done      -> pure rho
    st :> sts -> eval st rho >>= eval sts

-- We can finally define what it means to run a program: run the list
-- of statements using an empty environment to begin with and return
-- `()` if the evaluation is a success.

runProgram :: Program -> WriterT String (Either Error) ()
runProgram (Program p) = () <$ eval p empty

