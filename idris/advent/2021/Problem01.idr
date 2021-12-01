module Problem01

import Data.List
import Data.Maybe
import Data.String
import System
import System.File

%default total

fail : String -> IO ()
fail err = do putStrLn ("*** Error: " ++ err); exitFailure

measure : List Nat -> Nat
measure [] = 0
measure (x :: xs) = go 0 x xs where

  go : Ord a => Nat -> a -> List a -> Nat
  go acc bd [] = acc
  go acc bd (x :: xs) = go (ifThenElse (bd < x) S id acc) x xs

sliding : List Nat -> Nat
sliding xs =
  let dtail = fromMaybe [] . tail' in
  measure (zipWith3 (\m, n, p => m + n + p) xs (dtail xs) (dtail $ dtail xs))

main : IO ()
main = do
  [_,fp] <- getArgs
    | _ => fail "Expected a file name"
  Right content <- assert_total (readFile fp)
    | Left err => fail (show err)
  let vals : List Nat := map cast (lines content)
  putStrLn $ "Measure: " ++ show (measure vals)
  putStrLn $ "Sliding: " ++ show (sliding vals)
