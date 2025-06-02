{-# LANGUAGE LambdaCase #-}

import System.Random
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

type Location = String
type Value = Integer

data Predicate
  = MapsTo Location Value
  | And Predicate Predicate


type Model = Map Location Value

toModel :: Predicate -> Model
toModel = go Map.empty where

  go :: Model -> Predicate -> Model
  go m = \case
    MapsTo l v
      | l `Map.member` m -> error (l ++ " declared more than once")
      | otherwise -> Map.insert l v m
    And p q -> go (go m p) q

instance Show Predicate where
  show p = '{' : go p ++ "}" where
    go = \case
      MapsTo l v -> l ++ " -> " ++ show v
      And p q -> go p ++ ", " ++ go q

data Expr
  = Var Location
  | Val Integer
  | Add Expr Expr

eval :: Model -> Expr -> Integer
eval m = \case
  Var l -> fromMaybe (error (l ++ " not in scope")) (Map.lookup l m)
  Val i -> i
  Add s t -> eval m s + eval m t

instance Show Expr where
  showsPrec d = \case
    Var l -> showString l
    Add p q -> showParen (d > 0) $
      showsPrec 0 p .
      showString " + " .
      showsPrec 1 q

data Command
  = Assign Location Expr

execute :: Model -> Command -> Model
execute m (Assign l v) = Map.insert l (eval m v) m

instance Show Command where
  show (Assign l e) = l ++ " := " ++ show e

check :: Predicate -> Command -> Predicate -> Bool
check p c q = execute (toModel p) c == toModel q
