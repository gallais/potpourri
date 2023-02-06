module Lib

import Data.Buffer
import Data.Vect

%default total

export
failWith : String -> a
failWith str = assert_total (idris_crash str)

export
etaPair : (p : (a, b)) -> p === (fst p, snd p)
etaPair (t, u) = Refl

parameters (buf : Buffer)

  export
  setInts : Int -> Vect n Int -> IO ()
  setInts start [] = pure ()
  setInts start (i :: is)
    = do setInt buf start i
         setInts (start + 8) is
