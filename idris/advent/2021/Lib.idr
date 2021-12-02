module Lib

import System

%default total

export
fail : String -> IO ()
fail err = do putStrLn ("*** Error: " ++ err); exitFailure
