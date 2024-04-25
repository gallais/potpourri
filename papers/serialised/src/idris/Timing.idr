module Timing

import Data.Vect
import Data.Singleton
import Data.Serialisable.Desc
import Data.Serialisable.Data
import Data.Serialisable.Pointer
import Data.Serialisable.Tree

import System.GC
import System.Clock
import Data.String
import Data.Maybe

import System
import System.File

range : List Nat
range = [5..20]

samples : Nat
samples = 25

measure : IO () -> IO (Clock Duration)
measure act = do
  -- garbage collect what's not your responsibility
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

record CSVEntry (n : Nat) where
  constructor MkCSVEntry
  entrySize   : Nat
  entryValues : Vect n (Clock Duration)

Show (CSVEntry _) where
  show (MkCSVEntry si svs)
    = joinBy "," $ ("\{show si}" ::)
    $ map (show . toNano)
    $ toList svs

mkCSVEntry : Nat -> Vect n (IO ()) -> IO (CSVEntry n)
mkCSVEntry size acts = do
  timess <- for acts $ \ act =>
              for [1..samples] $ const $ toNano <$> measure act
  pure $ MkCSVEntry
    { entrySize   = size
    , entryValues = map (\ times => fromNano (sum times `div` cast samples)) timess
    }

csv : (name : String) ->
      (topics : Vect n String) ->
      (test : Nat -> IO (CSVEntry n)) ->
      IO ()
csv name topics test = do
   entries <- for range test
   Right () <- writeFile "\{name}.csv" $ unlines
                (joinBy "," ("size" :: toList topics)
                 :: map show entries)
     | Left err => die (show err)
   pure ()

takeApart :
  (name : String) ->
  (f : ATree -> a) ->
  (act : forall t. Pointer.Mu Tree t -> IO (Singleton (f t))) ->
  IO ()
takeApart name f act
  = csv name ["data", "pointer"] $ \ n => do

    let t = full n
    st <- execSerialising (serialise t)

    mkCSVEntry n $ map ignore
      [ map (f <$>) (deserialise st)
      , act st
      ]



-- If the family a is sufficiently precise, we don't need to use
-- the Singleton stuff to get sensible results!
takeApart' :
  (name : String) ->
  (0 a : ATree -> Type) ->
  (f : (t : ATree) -> (a t)) ->
  (act : forall t. Pointer.Mu Tree t -> IO (a t)) ->
  IO ()
takeApart' name a f act
  = csv name ["data", "pointer"] $ \ n => do

      let t = full n
      st <- execSerialising (serialise t)

      mkCSVEntry n $
        [ do t <- deserialise st
             let _ = f (getSingleton t)
             pure ()
        , ignore (act st)
        ]

serialise :
  (name : String) ->
  {cs : Data nm} ->
  {0 f : ATree -> Data.Mu cs} ->
  (acts : Vect n (String, forall t. Pointer.Mu Tree t -> Serialising cs (f t))) ->
  IO ()
serialise name acts
  = csv name (map fst acts) $ \ n => do

      let t = full n
      ptr <- execSerialising (serialise t)

      let test : (forall t. Pointer.Mu Tree t -> Serialising cs (f t)) -> IO ()
               := \ act => ignore (execSerialising (act ptr))
      mkCSVEntry n (map (test . snd) acts)

main : IO ()
main = do
  let range = [5..20]
  takeApart "sum" Data.sum Pointer.sum
  takeApart "rightmost" Data.rightmost Pointer.rightmost
  takeApart' "find" (Maybe . Path 120) (Data.find 120) (Pointer.find 120)
  serialise "map"
    [ ("data", deepMap (+100))
    , ("pointer", Pointer.map (+100))]
  serialise "swap"
    [ ("data", dataSwap)
    , ("pointer", deepSwap)
    , ("primitive", Pointer.swap)
    ]
