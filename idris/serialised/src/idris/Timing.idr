module Timing

import Data.Singleton
import Serialised.Desc
import SaferIndexed

import System.Clock
import Data.String
import Data.Maybe

measure : IO () -> IO (Clock Duration)
measure act = do
  start <- clockTime Process
  startgc <- clockTime GCReal
  () <- act
  end <- clockTime Process
  endgc <- clockTime GCReal
  let dfltClock = MkClock 0 0
  let gctime = fromMaybe dfltClock (timeDifference <$> endgc <*> startgc)
  let time = timeDifference (timeDifference end start) gctime
  let stime = showTime 2 9
  putStrLn "GC Time \{stime gctime}"
  putStrLn "Time \{stime time}"
  pure time

header : String -> IO ()
header msg = do
  putStrLn (replicate 72 '-')
  putStrLn msg

test : Show a =>
       (name : String) ->
       (f : ATree -> a) ->
       (act : forall t. Pointer.Mu Tree t -> IO (Singleton (f t))) ->
       (n : Nat) -> IO (Clock Duration, Clock Duration)
test name f act n = do
  putStrLn "\n\n"
  header "Size \{show n}"
  let t = full n
  putStrLn "Data tree \{name}: \{show $ f t}"
  st <- execSerialising (serialise t)
  putStrLn "Pointer tree \{name}: \{show !(act st)}"

  header "Timing pointer-based operation"
  time1 <- measure (do
    s <- act st
    putStrLn "\{name}: \{show s}")

  header "Timing deserialisation-based operation"
  time2 <- measure (do
    t <- deserialise st
    let s = f (getSingleton t)
    putStrLn "\{name}: \{show s}")

  pure (time1, time2)

main : IO ()
main = do
--   traverse_ (test "Sum" Data.sum Pointer.sum) [15..20]
  traverse_ (test "Rightmost" Data.rightmost Pointer.rightmost) [15..20]

  putStrLn "\n\n"
  header "Swap variants: using copy vs. deepCopy"
  let t = full 20
  t <- execSerialising (serialise t)
  () <$ measure (() <$ swap t)
  () <$ measure (() <$ deepSwap t)
