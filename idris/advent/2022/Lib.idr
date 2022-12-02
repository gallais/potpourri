module Lib

import public Data.String
import public System
import System.File

%default total

export
getInput : IO String
getInput = do
  [_,fp] <- getArgs
    | _ => die "Expected a file name"
  Right content <- assert_total (readFile fp)
    | Left err => die (show err)
  pure content
