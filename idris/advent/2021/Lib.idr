module Lib

import System
import System.File

%default total

export
fail : String -> IO a
fail err = do putStrLn ("*** Error: " ++ err); exitFailure

export
getInput : IO String
getInput = do
  [_,fp] <- getArgs
    | _ => fail "Expected a file name"
  Right content <- assert_total (readFile fp)
    | Left err => fail (show err)
  pure content
