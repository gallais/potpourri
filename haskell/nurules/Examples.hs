{-# OPTIONS -Wall #-}

module Examples where

import Data.Void
import Language
import TypeCheck
import FancyDomain

idType :: Check a
idType = piAbs Set $ piAbs (var Nothing) $ var $ Just Nothing

idTerm :: Check a
idTerm = lamAbs $ lamAbs $ var Nothing

plus :: Check a
plus =
  lamAbs {- m -} $
  lamAbs {- n -} $
    Emb $ Cut (Var $ Just Nothing) $
    [ Rec (lamAbs Nat) (var Nothing) (lamAbs $ lamAbs $ Suc $ var Nothing) ]

four :: Check a
four = Emb $ Cut (Ann plus (piAbs Nat $ piAbs Nat $ Nat)) $ [ App two , App two ]
  where two = Suc $ Suc Zro

data TypeCheck = TypeCheck (Type Void) (Check Void)
data Eval      = Eval      (Check Void)

instance Show TypeCheck where
  show (TypeCheck ty te) =
    maybe "False: " (const "True:  ") (check absurd ty te)
    ++ show te ++ "\n       isOfType\n       " ++ show ty

instance Show Eval where
  show (Eval te) =
      "           " ++ show te ++
    "\nreduces to " ++ show (normCheck te)

main :: IO ()
main = do
  print $ TypeCheck (piAbs Nat $ piAbs Nat Nat) plus
  print $ TypeCheck (piAbs Nat Nat) four
  print $ TypeCheck Nat four

  print $ Eval four
