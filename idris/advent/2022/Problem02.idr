module Problem02

import Lib

%default total

data Move = Rock | Paper | Scissors
data Outcome = Lose | Draw | Win

parseOpponent : Char -> Maybe Move
parseOpponent 'A' = pure Rock
parseOpponent 'B' = pure Paper
parseOpponent 'C' = pure Scissors
parseOpponent _ = Nothing

parsePlayer : Char -> Maybe Move
parsePlayer 'X' = pure Rock
parsePlayer 'Y' = pure Paper
parsePlayer 'Z' = pure Scissors
parsePlayer _ = Nothing

parseOutcome : Char -> Maybe Outcome
parseOutcome 'X' = pure Lose
parseOutcome 'Y' = pure Draw
parseOutcome 'Z' = pure Win
parseOutcome _ = Nothing

parseMoves : String -> Maybe (Move, Move)
parseMoves str = case map unpack (words str) of
  [[op],[pl]] => [| (parseOpponent op, parsePlayer pl) |]
  cs => Nothing

parseMO : String -> Maybe (Move, Outcome)
parseMO  str = case map unpack (words str) of
  [[op],[pl]] => [| (parseOpponent op, parseOutcome pl) |]
  cs => Nothing

outcome : (opponent, player : Move) -> Outcome
outcome Rock Paper = Win
outcome Paper Rock = Lose
outcome Scissors Paper = Lose
outcome Paper Scissors = Win
outcome Rock Scissors = Lose
outcome Scissors Rock = Win
outcome _ _ = Draw

moveScore : Move -> Nat
moveScore Rock = 1
moveScore Paper = 2
moveScore Scissors = 3

outcomeScore : Outcome -> Nat
outcomeScore Lose = 0
outcomeScore Draw = 3
outcomeScore Win = 6

pickMove : (them : Move) -> (out : Outcome) -> (me : Move ** outcome them me === out)
pickMove Rock Lose = (Scissors ** Refl)
pickMove Rock Draw = (Rock ** Refl)
pickMove Rock Win = (Paper ** Refl)
pickMove Paper Lose = (Rock ** Refl)
pickMove Paper Draw = (Paper ** Refl)
pickMove Paper Win = (Scissors ** Refl)
pickMove Scissors Lose = (Paper ** Refl)
pickMove Scissors Draw = (Scissors ** Refl)
pickMove Scissors Win = (Rock ** Refl)

part1 : List (Move, Move) -> Nat
part1 = sum . map (\ (them, me) => moveScore me + outcomeScore (outcome them me))

part2 : List (Move, Outcome) -> Nat
part2 = sum . map (\ (them, out) => moveScore (fst (pickMove them out)) + outcomeScore out)

main : IO ()
main = do
  cnt <- lines <$> getInput
  let moves = mapMaybe parseMoves cnt
  let mos = mapMaybe parseMO cnt
  putStrLn "Part 1: \{show (part1 moves)}"
  putStrLn "Part 2: \{show (part2 mos)}"
