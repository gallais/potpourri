module Timing

import Data.Singleton
import Serialised.Desc
import SaferIndexed

import System.Clock
import Data.String
import Data.Maybe

test : (n : Nat) -> IO (Clock Duration, Clock Duration)
test n = do
  putStrLn "\n\n"
  putStrLn (replicate 72 '-')
  putStrLn "Size \{show n}"
  let t = full n
  putStrLn "Data tree sum: \{show $ Tree.sum t}"
  st <- execSerialising (serialise t)
  putStrLn "Pointer tree sum: \{show !(Pointer.sum st)}"
  let stime = showTime 2 9

  let dfltClock = MkClock 0 0

  putStrLn (replicate 72 '-')
  putStrLn "Timing pointer-based operation"
  start1 <- clockTime Process
  startgc1 <- clockTime GCReal
  s <- Pointer.sum st
  putStrLn "Sum: \{show s}"
  end1 <- clockTime Process
  endgc1 <- clockTime GCReal
  let gctime1 = fromMaybe dfltClock (timeDifference <$> endgc1 <*> startgc1)
  let time1 = timeDifference (timeDifference end1 start1) gctime1
  putStrLn "GC Time \{stime gctime1}"
  putStrLn "Time \{stime time1}"


  putStrLn (replicate 72 '-')
  putStrLn "Timing deserialisation-based operation"
  start2 <- clockTime Process
  startgc2 <- clockTime GCReal
  t <- deserialise st
  let s = Tree.sum (getSingleton t)
  putStrLn "Sum: \{show s}"
  end2 <- clockTime Process
  endgc2 <- clockTime GCReal
  let gctime2 = fromMaybe dfltClock (timeDifference <$> endgc1 <*> startgc1)
  let time2 = timeDifference (timeDifference end2 start2) gctime2
  putStrLn "GC Time \{stime gctime2}"
  putStrLn "Time \{stime time2}"


  pure (time1, time2)

main : IO ()
main = traverse_ test [15..20]
