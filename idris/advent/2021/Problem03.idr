module Problem03

import Data.List
import Data.List1
import Data.SnocList
import Data.String
import Lib

%default total

data Bit = O | I

Eq Bit where
  O == O = True
  I == I = True
  _ == _ = False

toBit : Char -> Maybe Bit
toBit '0' = Just O
toBit '1' = Just I
toBit _ = Nothing

namespace Bit

  export
  toNat : Bit -> Nat
  toNat O = 0
  toNat I = 1

toBits : String -> Maybe (List Bit)
toBits = traverse toBit . unpack

record Count where
  constructor MkCount
  zeros : Nat
  ones  : Nat

toCount : Bit -> Count
toCount O = MkCount 1 0
toCount I = MkCount 0 1

toNat : List Bit -> Nat
toNat = foldl (\ acc, d => 2 * acc + toNat d) 0

add : (c, d : Count) -> Count
add (MkCount m n) (MkCount p q) = MkCount (m + p) (n + q)

mkRating : (Count -> Bit) ->
           SnocList Bit -> List (List1 Bit) -> List Bit
mkRating measure acc [bs] = acc <>> forget bs
mkRating measure acc [] = acc <>> []
mkRating measure acc bitss
  = let c = foldr (add . toCount . head) (MkCount 0 0) bitss in
    let bit = measure c in
    let bitss = flip mapMaybe bitss $ \ (x ::: xs) =>
                  do guard (x == bit)
                     fromList xs
    in assert_total $ mkRating measure (acc :< bit) bitss

main : IO ()
main = do
  content <- getInput
  let Just bitss@(l :: _) = traverse {f = Maybe} toBits (lines content)
    | _ => fail "Invalid input"
  let start = MkCount 0 0 <$ l
  let freqs : List Count := foldr (zipWith (add . toCount)) start bitss
  let gamma   = toNat $ map (\ c => ifThenElse (c.zeros > c.ones) O I) freqs
  let epsilon = toNat $ map (\ c => ifThenElse (c.ones > c.zeros) O I) freqs
  putStrLn "Gamma rate: \{show gamma}"
  putStrLn "Epsilon rate: \{show epsilon}"
  let energy = gamma * epsilon
  putStrLn "Energy consumption: \{show energy}"
  let rating = \ c => mkRating c [<] (mapMaybe fromList bitss)
  let oxygen = toNat $ rating (\ c => ifThenElse (c.zeros > c.ones) O I)
  let co2    = toNat $ rating (\ c => ifThenElse (c.zeros > c.ones) I O)
  putStrLn "Oxygen rating: \{show oxygen}"
  putStrLn "CO2 rating: \{show co2}"
  let life = oxygen * co2
  putStrLn "Life support rating: \{show life}"
