module Handcli where

import Data.List (intercalate)
import Data.List.Split (chunksOf)

-- ┌────────────────┐
-- │ Hello          │
-- └────────────────┘

box :: [String] -> String
box ls =
  let w = maximum $ map length ls in
  intercalate "\n"
    $ ('┌' : replicate  (w + 2) '─' ++ "┐")
    : map (\ l -> "│ " ++ l ++ replicate (w - length l) ' ' ++ " │") ls
    ++ ['└' : replicate  (w + 2) '─' ++ "┘"]

wobbox :: [String] -> String
wobbox ls =
  let w = maximum $ map length ls in
  intercalate "\n"
    $ ('╭' : replicate  (w + 2) '─' ++ "╮")
    : map (\ l -> "│ " ++ l ++ replicate (w - length l) ' ' ++ " │") ls
    ++ ['╰' : replicate  (w + 2) '─' ++ "╯"]

tbox :: Int -> String -> String -> [String] -> String
tbox colour t loc ls =
  let w = maximum $ 80 : map length ls in
  let e = length t in
  intercalate "\n"
    $ (" ╭" ++ replicate (e + 2) '─' ++ "┬" ++ replicate  (w - e - 1) '─' ++ "╮")
    : (" │ \ESC[" ++ show colour ++ "m" ++ t ++ "\ESC[0m │ " ++ loc ++ replicate (w - e - length loc - 3) ' ' ++ " │")
    : (" ├" ++ replicate (e + 2) '─' ++ "┘" ++ replicate (w - e - 2) ' ' ++ " │")
    : map (\ l -> " │ " ++ l ++ replicate (w - length l) ' ' ++ " │") ls
    ++ [" ╰" ++ replicate  (w + 2) '─' ++ "╯"]

lorem :: [String]
lorem = chunksOf 80 "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum."


test :: IO ()
test = putStr $ unlines
  [ tbox 103 "Warning"
     "/home/gallais/languages/agda/ViewSplit.agda:1,1-35"
     [ "Cannot set OPTIONS pragma --rewriting with safe flag."
     ]
  , tbox 101 "Error"
     "/home/gallais/languages/agda/ViewSplit.agda:23,15-17"
     [ "(n₁ : ℕ) → View (c1 n₁) !=< View (c1 n)"
     , "when checking that the expression c1 has type View (c1 n)"
     ]
  ]
