module Data.IORef.Indexed

import Control.Linear.LIO
import Data.IORef
import Data.Linear.Notation
import Data.List.Quantifiers
import Data.Singleton
import Data.So
import System
import System.Concurrency
import System.Concurrency.Linear
import System.Random

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
0 valueOf : Owned {a} c v -> a
valueOf _ = v

public export
record Allocated {a : Type} (v : a) where
  constructor MkAllocated
  {0 cell : Cell a}
  1 runAllocated : Owned cell v

export
new : LinearIO io => (v : a) -> L1 io (Allocated v)
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
write : LinearIO io => (1 _ : Owned c _) -> (v : a) -> L1 io (Owned c v)
write (MkOwned (MkCell c)) v = do
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

public export
data Pointers : {as : List Type} -> All Cell as -> Type where
  Nil : Pointers []
  (::) : (1 _ : Owned {a} c v) -> Pointers cs -> Pointers (c :: cs)

public export
0 Predicate : List Type -> Type
Predicate [] = Type
Predicate (a :: as) = a -> Predicate as

public export
0 applyPredicate : Predicate as -> Pointers {as} c -> Type
applyPredicate p [] = p
applyPredicate p (o :: os) = applyPredicate (p (valueOf o)) os

public export
record WithInvariant {as : List Type} (cs : All Cell as) (p : Predicate as) where
  constructor (#)
  1 fst : Pointers cs
  0 snd : applyPredicate p fst

export
data Lock : {as : List Type} -> All Cell as -> Predicate as -> Type where
  MkLock :
    {0 cs : All Cell as} ->
    {0 p : Predicate as} ->
    Mutex ->
    (1 locked : WithInvariant cs p) ->
    Lock cs p

export
mkLock : LinearIO io =>
  {0 cs : All Cell as} ->
  (1 os : Pointers cs) ->
  (0 p : Predicate as) ->
  (0 _ : applyPredicate p os) -> L io (Lock cs p)
mkLock os p prf = do
  mutex <- makeMutex
  let v = MkLock mutex (os # prf)
  assert_linear pure v

export
withLock : LinearIO io =>
  Lock cs p ->
  (WithInvariant cs p -@ L1 io (LPair (WithInvariant cs p) b))
  -@ L1 io b
withLock (MkLock mutex locked) f = do
  mutexAcquire mutex
  v # w <- f locked
  let () = assert_linear (const ()) v
  mutexRelease mutex
  pure1 w

public export
OwnedEven : Predicate [Nat]
OwnedEven n = (p : Nat ** n === 2 * p)

plus2 : (p : Nat ** n === 2 * p) -> (p : Nat ** 2 + n === 2 * p)
plus2 (p ** prf) = (S p ** ?ag)

export
printAndIncr : LinearIO io => String -> Lock [c] OwnedEven -> L1 io ()
printAndIncr identity l = do
  sec <- randomRIO {a = Int32} (0, 10)
  putStrLn "\{identity}: sleeping for \{show sec}00 milliseconds"
  usleep @{%search} (cast sec * 10_000) @{believe_me Oh}
  withLock l $ \ ([ptr] # prf) => do
    (ptr # Val n) <- read ptr
    putStrLn "\{identity}: got \{show n}, putting \{show (2 + n)} back in"
    ptr <- write ptr (2 + n)
    pure1 (([ptr] # plus2 prf) # ())

main : IO ()
main = run $ do
  MkAllocated ptr  <- new 0
  lock <- mkLock [ptr] OwnedEven (0 ** Refl)
  (() # ()) <- par1 (printAndIncr "A" lock) (printAndIncr "B" lock)
  pure ()
