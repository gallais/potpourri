module Alice

import Data.DPair
import Data.List
import Data.Singleton
import Data.Vect

import Serialised.Desc
import SaferIndexed

import System.Random
import System

import Control.ANSI

%default total

randomTree : Bool -> Nat -> IO ATree
randomTree b Z = pure leaf
randomTree b (S n)
  = do False <- (b &&) . (0 ==) <$> randomRIO (the Int32 0, 6)
         | _ => pure leaf
       l <- randomTree True n
       b <- cast <$> randomRIO (the Int32 0, 255)
       r <- randomTree True n
       pure (node l b r)

data Options : Type where
  Generate : (filename : String) -> Options
  Load     : (filename : String) -> Options

help : String
help = "Usage: Alice [generate|load] FILE"

options : List String -> Maybe Options
options ["generate", fp] = pure (Generate fp)
options ["load", fp] = pure (Load fp)
options _ = Nothing

main : IO ()
main = do
  printLn (bolden "Hello I am Alice, written in Idris!")

  -- Get the filename in which to store the tree
  Just opts <- (options <=< tail') <$> getArgs
    | Nothing => die help

  case opts of

    Generate fp => do
      -- Generate a random tree and get a pointer for it
      tree <- randomTree False 3

      putStrLn "I just generated the following random tree:"
      putStr (Tree.showi "  " tree)

      putStrLn "And I am now writing it in file \{fp}."
      tree <- execSerialising (serialise tree)
      writeToFile fp tree

    Load fp => do
      Evidence _ tree <- initFromFile Tree fp
      putStrLn "I just read the following tree from file \{fp}:"
      tree <- deserialise tree
      putStrLn (Tree.showi "  " (getSingleton tree))
