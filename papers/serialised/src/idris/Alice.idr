module Alice

import Serialised.Desc
import SaferIndexed

import System.Random
import System

import Control.ANSI

%default total

randomTree : Nat -> IO ATree
randomTree Z = pure leaf
randomTree (S n)
  = do False <- (0 ==) <$> randomRIO (the Int32 0, 10)
         | _ => pure leaf
       l <- randomTree n
       b <- cast <$> randomRIO (the Int32 0, 255)
       r <- randomTree n
       pure (node l b r)

main : IO ()
main = do
  printLn (bolden "Hello I am Idris!")

  -- Get the filename in which to store the tree
  (_ :: fp :: _) <- getArgs
    | _ => die "Expected a file name as an argument"

  -- Generate a random tree and get a pointer for it
  tree <- randomTree 2

  putStrLn "I just generated the following random tree:"
  putStr (Tree.show tree)

  putStrLn "And I am now writing it in file \{fp}"
  tree <- execSerialising (serialise tree)
  writeToFile fp tree
