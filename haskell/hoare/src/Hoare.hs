{-# LANGUAGE LambdaCase #-}

module Hoare where

import Data.List (intercalate, foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

data Value v = MkValue
  { constant :: Integer
  , variables :: Map v Integer
  } deriving Eq

------------------------------------------------------------------------
-- Expressions

data Expr v
  = Var v
  | Val Integer
  | Add (Expr v) (Expr v)
  | Sub (Expr v) (Expr v)

add :: Ord v => Value v -> Value v -> Value v
add (MkValue k1 m1) (MkValue k2 m2) = MkValue
  (k1 + k2)
  (Map.filter (/= 0) $ Map.unionWith (+) m1 m2)

neg :: Ord v => Value v -> Value v
neg (MkValue k m) = MkValue (negate k) (negate <$> m)

eval :: (Show v, Ord w) => (v -> Maybe (Value w)) -> Expr v -> Value w
eval m = \case
  Var l -> fromMaybe (error (show l ++ " not in scope")) (m l)
  Val i -> MkValue i Map.empty
  Add s t -> add (eval m s) (eval m t)
  Sub s t -> add (eval m s) (neg (eval m t))

instance Show v => Show (Expr v) where
  showsPrec d = \case
    Var l -> showsPrec d l
    Val i -> showsPrec d i
    Add p q -> showParen (d > 0) $
      showsPrec 0 p .
      showString " + " .
      showsPrec 1 q
    Sub p q -> showParen (d > 0) $
      showsPrec 1 p .
      showString " - " .
      showsPrec 1 q

------------------------------------------------------------------------
-- Predicates


newtype Logical = MkLogical { getLogical :: String } deriving (Eq, Ord)
newtype Location = MkLocation { getLocation :: String } deriving (Eq, Ord)

variable :: Logical -> Value Logical
variable l = MkValue 0 (Map.singleton l 1)

instance Show Logical where show = getLogical
instance Show Location where show = getLocation

data Statement
  = MapsTo Location (Expr Logical)

newtype Predicate = MkPredicate { getPredicate :: [Statement] }

type Model = Map Location (Value Logical)

statement :: Model -> Statement -> Model
statement m (MapsTo l v)
  | l `Map.member` m = error (show l ++ " declared more than once")
  | otherwise = Map.insert l (eval (pure . variable) v) m

predicate :: Predicate -> Model
predicate = foldl' statement Map.empty . getPredicate

instance Show Statement where
  show (MapsTo l v) = show l ++ " -> " ++ show v

instance Show Predicate where
  show p = '{' : intercalate ", " (show <$> getPredicate p) ++ "}"

data Command
  = Assign Location (Expr Location)

execute :: Model -> Command -> Model
execute m (Assign l v) = Map.insert l (eval (flip Map.lookup m) v) m

instance Show Command where
  show (Assign l e) = show l ++ " := " ++ show e

newtype Program = MkProgram { runProgram :: [Command] }

run :: Model -> Program -> Model
run m p = foldl' execute m (runProgram p)

instance Show Program where
  show (MkProgram p) = intercalate ";\n" (show <$> p)

data Claim = MkClaim
  { precondition :: Predicate
  , program :: Program
  , postcondition :: Predicate
  }

instance Show Claim where
  show (MkClaim pre prog post) = intercalate "\n" [show pre, show prog, show post]


check :: Claim -> Bool
check (MkClaim p c q) = run (predicate p) c == predicate q
