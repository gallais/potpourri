module Problem01

import Data.List1
import Lib

%default total

record Elf where
  constructor MkElf
  carrying : List Nat

parseElves : String -> List Elf
parseElves cnt = do
  let ls = lines cnt
  map (MkElf . map cast) $ forget $ split null ls

part1 : List Nat -> IO Nat
part1 cals = case cals of
  [] => die "Expected at least one elf"
  (hd :: _) => pure hd

part2 : List Nat -> IO Nat
part2 cals = case cals of
  (e1 :: e2 :: e3 :: _) => pure (e1 + e2 + e3)
  _ => die "Expected at least three elves"

main : IO ()
main = do
  cnt <- getInput
  let elves = parseElves cnt
  let calories = sortBy (flip compare) (map (sum . carrying) elves)
  putStrLn "Part 1: \{show !(part1 calories)}"
  putStrLn "Part 2: \{show !(part2 calories)}"
