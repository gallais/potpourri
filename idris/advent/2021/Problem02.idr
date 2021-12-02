module Problem02

import Data.String
import System
import System.File

import Lib

%default total

data Direction = Fwd | Up | Down
record Command where
  constructor MkCommand
  direction : Direction
  quantity  : Nat

parse : List String -> List Command
parse (x :: y :: xs) = MkCommand dir (cast y) :: parse xs where

  dir : Direction
  dir = case x of
    "forward" => Fwd
    "up" => Up
    "down" => Down
    _ => Fwd -- scandalously returning a default value

parse _ = []

record Position where
  constructor MkPosition
  depth : Nat
  advance : Nat

move : Command -> Position -> Position
move c = case c.direction of
  Fwd  => { advance $= (c.quantity +) }
  Up   => { depth   $= (`minus` c.quantity) }
  Down => { depth   $= (c.quantity +) }

record Position2 where
  constructor MkPosition2
  depth : Nat
  advance : Nat
  aim : Nat

move2 : Command -> Position2 -> Position2
move2 c pos = case c.direction of
  Fwd  => { advance $= (c.quantity +)
          , depth   $= ((c.quantity * pos.aim) +)
          } pos
  Up   => { aim     $= (`minus` c.quantity) } pos
  Down => { aim     $= (c.quantity +) } pos

main : IO ()
main = do
  [_,fp] <- getArgs
    | _ => fail "Expected a file name"
  Right content <- assert_total (readFile fp)
    | Left err => fail (show err)
  let cmds = parse (assert_total $ words content)
  let pos  = foldl (flip move) (MkPosition 0 0) cmds
  putStrLn $ "Arrived at advance \{show pos.advance} and depth \{show pos.depth}"
  putStrLn $ "Answer: \{show (pos.advance * pos.depth)}"
  let pos2 = foldl (flip move2) (MkPosition2 0 0 0) cmds
  putStrLn $ "Arrived at advance \{show pos2.advance} and depth \{show pos2.depth}"
  putStrLn $ "Answer: \{show (pos2.advance * pos2.depth)}"
