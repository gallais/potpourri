{-# OPTIONS -Wall #-}

module Examples where

import Data.Void
import Data.List
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

eight :: Check a
eight =
  Bnd (Let $ Ann plus $ piAbs Nat $ piAbs Nat Nat) $
  Bnd (Let $ Ann four Nat) $
  Emb $ Cut (Var $ Just Nothing) [ App (var Nothing) , App (var Nothing) ]

data Example =
    TypeCheck (Type Void, Check Void)
  | Eval      (Check Void)

newtype Examples = Examples { examples :: [Example] }

ppTypeCheck :: (Type Void, Check Void) -> (Int, String)
ppTypeCheck (ty , te) =
  let (m, strTe) = padLines $ lines $ show te
      (n, strTy) = padLines $ lines $ show ty
  in (max m n,
     "TypeOf | " ++ strTe
     ++ '\n' : maybe "Isn't  | " (const "Is     | ") (check absurd ty te) ++ strTy)

ppEval :: Check Void -> (Int, String)
ppEval te =
  let (m, strTe) = padLines $ lines $ show te
      (n, strNf) = padLines $ lines $ show $ normCheck te
  in (max m n,
     "Eval   | " ++ strTe
     ++ '\n' : "Gives  | " ++ strNf)

ppExample :: Example -> (Int, String)
ppExample (TypeCheck tyte) = ppTypeCheck tyte
ppExample (Eval t)         = ppEval t

instance Show Examples where
  show (Examples exs) =
    let (m , strs) =
          foldl (\ (ihm , ihstrs) ex ->
            let (n , str) = ppExample ex in
            (max ihm n, str : ihstrs))
          (0 , []) exs
    in
      replicate (9 + m) '-' ++ "\n"
      ++ intercalate ('\n' : replicate (9 + m) '-' ++ "\n") strs
      ++ '\n' : replicate (9 + m) '-'

padLines :: [String] -> (Int, String)
padLines []           = (0, [])
padLines [hd]         = (length hd, hd)
padLines xs@(hd : tl) = (n, str)
  where
    n   = maximum $ fmap length xs
    str = intercalate "\n" $ hd : fmap ("       | " ++) tl

main :: IO ()
main = do
  print $ Examples
          [ TypeCheck (piAbs Nat (piAbs Nat Nat), plus)
          , TypeCheck (piAbs Nat Nat            , four)
          , TypeCheck (Nat                      , four)
          , Eval      four
          , TypeCheck (Nat                      , eight)
          , Eval      eight
          ]
