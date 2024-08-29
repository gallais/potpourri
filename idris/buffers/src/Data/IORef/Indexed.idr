module Data.IORef.Indexed

import Control.Linear.LIO
import Data.IORef
import Data.Linear.Notation
import Data.List.Quantifiers
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

------------------------------------------------------------------------
-- Memory cells, ownership proofs, and basic combinators

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
||| The library should enforce the following global invariants:
||| 1. at any point, for a cell c there must be at most one proof (Owned c _)
||| 2. for every (Owned c v), c must contain a value equal to v
export
data Owned : (c : Cell a) -> (v : a) -> Type where
  MkOwned : (c : Cell a) -> Owned c v

||| Helper function to talk about the value that is in an
||| owned cell. This is useful for type-level programming
||| only as these values are meant to be runtime-erased.
public export
0 valueOf : Owned {a} c v -> a
valueOf _ = v

||| When we allocate a cell for a value, we get back the
||| fact an owned cell containing that value exists. But
||| we do not of course get to manipulate that cell directly
||| so it is erased.
public export
record Allocated {a : Type} (v : a) where
  constructor MkAllocated
  {0 cell : Cell a}
  1 runAllocated : Owned cell v

||| Provided we have an unrestricted value, we can allocate
||| a new cell that contains it. We then own that cell.
export
new : LinearIO io => (v : a) -> L1 io (Allocated v)
new v = do
  c <- newIORef v
  pure1 (MkAllocated $ MkOwned $ MkCell c)

||| Free a pointer to a cell provided that you own it.
||| The current IO refs are garbage collected so we simply
||| throw the ownership proof away.
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


------------------------------------------------------------------------
-- Locks guarding cells, and how to operate on them

-- In separation logic, a lock protects a set of memory locations
-- that can be accessed concurrently. Locks "ownership" can be
-- freely duplicated because opening one means acquiring a mutex
-- protecting the cell-dependent execution.
-- For proof purposes, they additionally come with an invariant
-- applying to the values stored in the memory locations.

||| This is a bit like `Owned` except that we do not
||| explicitly talk about the value that is stored.
||| It is used to list the cells that are guarded by
||| a given lock (cf. `Lock` below)
public export
data Pointers : {as : List Type} -> All Cell as -> Type where
  Nil : Pointers []
  (::) : (1 _ : Owned {a} c v) -> (1 _ : Pointers cs) -> Pointers (c :: cs)

||| An n-ary predicate over a heterogeneous list of values
public export
0 Predicate : List Type -> Type
Predicate [] = Type
Predicate (a :: as) = a -> Predicate as

||| Given an n-ary predicate and a list of owned cells,
||| we can state that the predicate holds of the values
||| stored in the cells
public export
0 applyPredicate : Predicate as -> Pointers {as} c -> Type
applyPredicate p [] = p
applyPredicate p (o :: os) = applyPredicate (p (valueOf o)) os

||| Packaging a linear list of owned cells together with
||| a proof the values they store respects a predicate.
||| The predicate is erased so that it cannot contain
||| runtime-relevant information.
||| This is the invariant that will need to be maintained
||| before the lock is released.
public export
record WithInvariant {as : List Type} (cs : All Cell as) (p : Predicate as) where
  constructor (#)
  1 fst : Pointers cs
  0 snd : applyPredicate p fst

||| A lock is indexed by the list of cells it protects and
||| a predicate specifying the invariant they need to respect.
||| Internally it's represented by the pairing of a mutex
||| and a linear list of ownership proofs of the cells
||| satisfying the invariant.
export
data Lock : {as : List Type} -> All Cell as -> Predicate as -> Type where
  MkLock :
    {0 cs : All Cell as} ->
    {0 p : Predicate as} ->
    Mutex ->
    (1 locked : WithInvariant cs p) ->
    Lock cs p

||| Given a linear list of cells satisfying a given predicate,
||| we can form a lock protecting the cells and using the
||| predicate as an invariant that must be maintained.
||| Lock ownership is freely duplicable as the mutex guarantees
||| only one threads really claims to own the protected cells
||| at any point in time. This is why the return type is
||| unrestricted.
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

||| If we own a lock, we can open it and obtain
||| 1. the ownership proofs of the cells it protects
||| 2. the proof the values in these cells satisfy the invariant
||| Once we are ready to close the lock, we need to
||| 1. return the ownership proofs of the protected cells
||| 2. prove that their (potentially different) contents still satisfy the invariant
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
