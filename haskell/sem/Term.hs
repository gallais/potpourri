module Term where

import Data.Void

data Term a =
  -- basic constructors
    Var a
  | App (Term a) (Term a)
  | Lam (Term (Maybe a))
  -- types
  | Pi (Term a) (Term (Maybe a))
  | Set Integer

newtype ClosedTerm = ClosedTerm { term :: Term Void }
