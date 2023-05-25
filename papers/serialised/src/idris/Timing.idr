module Timing

import Data.List
import Data.Singleton
import Serialised.Desc
import SaferIndexed

import System.GC
import System.Clock
import Data.String
import Data.Maybe

import System
import System.File

measure : IO () -> IO (Clock Duration)
measure act = do
  gc
  start <- clockTime Process
  () <- act
  end <- clockTime Process
  let time = timeDifference end start
  let stime = showTime 2 9
  putStrLn "Time \{stime time}"
  pure time

header : String -> IO ()
header msg = do
  putStrLn (replicate 72 '-')
  putStrLn msg

record CSVEntry where
  constructor MkCSVEntry
  entrySize : Nat
  entrySerialised : Clock Duration
  entryDeserialised : Clock Duration

Show CSVEntry where
  show (MkCSVEntry si ser deser)
    = joinBy "," $ ("\{show si}" ::)
    $ map (show . toNano)
    [ ser, deser ]

mkCSVEntry : Nat -> IO a -> IO b -> IO CSVEntry
mkCSVEntry n act1 act2 = do
  let range = the Nat 20
  times1 <- for [1..range] $ const $ toNano <$> measure (ignore act1)
  times2 <- for [1..range] $ const $ toNano <$> measure (ignore act2)
  pure $ MkCSVEntry
    { entrySize = n
    , entrySerialised = fromNano (sum times1 `div` cast range)
    , entryDeserialised = fromNano (sum times2 `div` cast range)
    }

deepVSshallow :
  {cs : Data nm} ->
  {0 f : ATree -> Data.Mu cs} ->
  (deep : forall t. Pointer.Mu _ t -> Serialising cs (f t)) ->
  (shallow : forall t. Pointer.Mu _ t -> Serialising cs (f t)) ->
  Nat -> IO CSVEntry
deepVSshallow deep shallow n = do
  t <- execSerialising (serialise $ full n)
  mkCSVEntry n (execSerialising $ deep t) (execSerialising $ shallow t)


dataVSpointer :
  (f : ATree -> a) ->
  (act : forall t. Pointer.Mu Tree t -> IO (Singleton (f t))) ->
  (n : Nat) -> IO CSVEntry
dataVSpointer f act n = do

  let t = full n
  st <- execSerialising (serialise t)

  mkCSVEntry n (act st) $ do
    t <- deserialise st
    pure (f (getSingleton t))

csv : (name : String) ->
      (range : List Nat) ->
      (test : (n : Nat) -> IO CSVEntry) ->
      IO ()
csv name range test = do
   entries <- for range $ test
   Right () <- writeFile "\{name}.csv" $ unlines
                ("size,serialised,deserialised"
                 :: map show entries)
     | Left err => die (show err)
   pure ()


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
  let range = [5..20]
  csv "sum"       range (dataVSpointer Data.sum Pointer.sum)
  csv "rightmost" range (dataVSpointer Data.rightmost Pointer.rightmost)
  csv "copy"      range (deepVSshallow deepCopy copy)
  csv "swap"      range (deepVSshallow deepSwap Pointer.swap)

{-
  traverse_ (test "Sum" Data.sum Pointer.sum) [15..20]
  traverse_ (test "Rightmost" Data.rightmost Pointer.rightmost) [15..20]

  putStrLn "\n\n"
  header "Copy variants: using copy vs. deepCopy vs. roundtripCopy"
  for_ [10..20] $ \ n => do
    header "Size \{show n}"
    let t = full n
    t <- execSerialising (serialise t)
    () <$ measure (() <$ execSerialising (copy t))
    () <$ measure (() <$ execSerialising (deepCopy t))
    () <$ measure (() <$ execSerialising (roundtripCopy t))

  putStrLn "\n\n"
  header "Levels variants: using levels vs. deepLevels"
  for_ [10..20] $ \ n => do
    header "Size \{show n}"
    () <$ measure (() <$ execSerialising (levels n))
    () <$ measure (() <$ execSerialising (deepLevels n))
-}
