{-# OPTIONS -Wall #-}

module Examples where

import Data.Void
import Language
import FancyDomain
import Equality

idType :: Check a
idType = piAbs Set $ piAbs (var Nothing) $ var $ Just Nothing

idTerm :: Check a
idTerm = lamAbs $ lamAbs $ var Nothing

plus :: Check a
plus =
  lamAbs {- m -} $
  lamAbs {- n -} $
    Emb $ Cut (Var $ Just Nothing) $
    [ Rec (piAbs Nat Nat) (var Nothing) (lamAbs $ lamAbs $ Suc $ var Nothing) ]

four :: Check a
four = Emb $ Cut (Ann plus (piAbs Nat $ piAbs Nat $ Nat)) $ [ App two , App two ]
  where two = Suc $ Suc Zro

main :: IO ()
main = do
  let twoTwice :: Check Void
      twoTwice = four
  let idNat :: Check Void
      idNat = Emb $ Cut (Ann idType Set) [ App Nat ]

  print twoTwice
  putStrLn "reduces to..."
  print $ norm twoTwice

  print idNat
  putStrLn "reduces to..."
  print $ norm idNat

  let llv :: Check Void
      llv = lamAbs $ Emb $ Var Nothing
      llvv :: Check Void
      llvv = lamAbs $ lamAbs $ Emb $ Cut (Var $ Just Nothing) [ App (Emb $ Var Nothing) ]
  print $ llv
  putStrLn "equals?"
  print $ llvv
  print $ eqNf (norm llv) (norm llvv)
