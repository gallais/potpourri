module lib where

import Data.List.Base as List
open import Data.Maybe.Base using (just)
open import Data.String.Base using (String)
open import IO
open import System.Environment

getInput : IO String
getInput = do
  args ← getArgs
  (just fp) ← pure (List.head args)
    where _ → pure ""
  readFiniteFile fp
