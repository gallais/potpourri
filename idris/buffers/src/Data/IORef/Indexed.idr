module Data.IORef.Indexed

import Control.Linear.LIO
import Data.IORef
import Data.Linear.Notation
import Data.Singleton
import System.Concurrency

%default total

||| Trust me, bro.
||| Used to reflect runtime-read information at the type level.
||| All usages should be proven safe according to the library's
||| invariants.
%unsafe
unsafeMkSingleton : (0 x : a) -> (val : a) -> Singleton x
unsafeMkSingleton x val = believe_me (Val val)

||| Wrapper whose constructor is not publicly exported
||| so that users do not get to use standard IORef functions
||| on it!
export
data Cell : Type -> Type where
  MkCell : IORef a -> Cell a

||| A proof of ownership of a cell allows one to read it,
||| and write it.
||| The proof is indexed by its content so as to allow
||| correct-by-construction programming. Intuitively,
||| a linear value of type (Owned c v) could be understood
||| as a (c ↦ v) predicate in separation logic.
||| The library should enforce the following gloabl invariants:
||| 1. for a cell c, there must be at most one proof (Owned c _)
||| 2. for every (Owned c v), c must contain a value equal to v
export
data Owned : (c : Cell a) -> (v : a) -> Type where
  MkOwned : (c : Cell a) -> Owned c v

public export
record Allocated {a : Type} (v : a) where
  constructor MkAllocated
  {0 cell : Cell a}
  1 runAllocated : Owned cell v

export
new : LinearIO io => (1 v : a) -> L1 io (Allocated v)
new v = do
  c <- assert_linear newIORef v
  pure1 (MkAllocated $ MkOwned $ MkCell c)

||| Free a pointer to a cell provided that you own it.
||| The current IO refs are garbage collected so we simply
||| throw the proof away.
export
free : LinearIO io => Owned c v -> L io ()
free (MkOwned _) = pure ()

||| Set the value of a cell provided we own the corresponding
||| pointer. We get back a new ownership proof with the updated
||| content.
export
set : LinearIO io => (v : a) -> Owned c _ -@ L1 io (Owned c v)
set v (MkOwned (MkCell c)) = do
  modifyIORef c (const v)
  pure1 (MkOwned (MkCell c))

||| Read the value of a cell provided we own the corresponding
||| pointer. We still own the pointer after reading from it.
||| The Singleton value we return means we get access to
||| a runtime value known to be equal to the specified content
||| of the cell.
export
read : LinearIO io => Owned c v -@ L1 io (LPair (Owned c v) (Singleton v))
read (MkOwned (MkCell c)) = do
  val <- readIORef c
  pure1 (MkOwned (MkCell c) # unsafeMkSingleton v val)
