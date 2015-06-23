module Term where

import Data.Void

data Term a =
  -- basic constructors
    Var a
  | App (Term a) (Term a)
  | Lam (Term (Maybe a))

newtype ClosedTerm = ClosedTerm { term :: Term Void }
