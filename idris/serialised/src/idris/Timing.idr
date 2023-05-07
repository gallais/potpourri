module Timing

import Data.Singleton
import Serialised.Desc
import SaferIndexed

import System.Clock
import Data.String
import Data.Maybe

test : Show a =>
       (name : String) ->
       (f : ATree -> a) ->
       (act : forall t. Pointer.Mu Tree t -> IO (Singleton (f t))) ->
       (n : Nat) -> IO (Clock Duration, Clock Duration)
test name f act n = do
  putStrLn "\n\n"
  putStrLn (replicate 72 '-')
  putStrLn "Size \{show n}"
  let t = full n
  putStrLn "Data tree \{name}: \{show $ f t}"
  st <- execSerialising (serialise t)
  putStrLn "Pointer tree \{name}: \{show !(act st)}"
  let stime = showTime 2 9

  let dfltClock = MkClock 0 0

  putStrLn (replicate 72 '-')
  putStrLn "Timing pointer-based operation"
  start1 <- clockTime Process
  startgc1 <- clockTime GCReal
  s <- act st
  putStrLn "\{name}: \{show s}"
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
  let s = f (getSingleton t)
  putStrLn "\{name}: \{show s}"
  end2 <- clockTime Process
  endgc2 <- clockTime GCReal
  let gctime2 = fromMaybe dfltClock (timeDifference <$> endgc1 <*> startgc1)
  let time2 = timeDifference (timeDifference end2 start2) gctime2
  putStrLn "GC Time \{stime gctime2}"
  putStrLn "Time \{stime time2}"


  pure (time1, time2)

main : IO ()
main = do
--   traverse_ (test "Sum" Data.sum Pointer.sum) [15..20]
  traverse_ (test "Rightmost" Data.rightmost Pointer.rightmost) [15..20]
