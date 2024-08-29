module Data.IORef.Indexed.Examples

import Control.Linear.LIO
import Data.IORef
import Data.Linear.Notation
import Data.List.Quantifiers
import Data.Nat
import Data.Singleton
import Data.So
import Syntax.PreorderReasoning
import System
import System.Concurrency
import System.Concurrency.Linear
import System.Random

import Data.IORef.Indexed

%default total

------------------------------------------------------------------------
-- Example: concurrent programs sharing a cell containing an even number

public export
IsEven : Predicate [Nat]
IsEven n = (p : Nat ** n === 2 * p)

plus2Even : IsEven n -> IsEven (2 + n)
plus2Even (p ** prf) = MkDPair (S p) $
  rewrite sym $ plusSuccRightSucc p (plus p 0) in
  cong (S . S) prf

squaredEven : IsEven n -> IsEven (n * n)
squaredEven (p ** prf) = MkDPair (p * (2 * p)) $ Calc $
  |~ n * n
  ~~ (2 * p) * (2 * p) ..>( cong (\ n => n * n) prf )
  ~~ 2 * (p * (2 * p)) ..<( multAssociative 2 p (2 * p) )


randomSleep : LinearIO io => String -> L io ()
randomSleep identity = do
  sec <- randomRIO {a = Int32} (0, 10)
  putStrLn "\{identity}: sleeping for \{show sec}00 milliseconds"
  usleep @{%search} (cast sec * 10_000) @{believe_me Oh}

get :
  LinearIO io =>
  String ->
  Owned {a = Nat} c v -@
  L1 io (LPair (Owned c v) (Singleton v))
get identity ptr = do
  randomSleep identity
  (ptr # Val n) <- read ptr
  putStrLn "\{identity}: read \{show n}"
  pure1 (ptr # Val n)

put :
  LinearIO io =>
  String ->
  (1 _ : Owned {a = Nat} c v) ->
  (w : Nat) ->
  L1 io (Owned c w)
put identity ptr w = do
  randomSleep identity
  ptr <- write ptr w
  putStrLn "\{identity}: wrote \{show w}"
  pure1 ptr

export
printAndUpdate :
  LinearIO io =>
  String ->
  (f : Nat -> Nat) ->
  (0 prfF : forall n. IsEven n -> IsEven (f n)) ->
  Lock [c] IsEven -> L1 io ()
printAndUpdate identity f prfF l = do
  randomSleep identity
  withLock l $ \ ([ptr] # prf) => do
    putStrLn "\{identity}: lock acquired"
    (ptr # Val n) <- get identity ptr
    ptr <- put identity ptr (f n)
    pure1 (([ptr] # prfF prf) # ())
  putStrLn "\{identity}: lock released"
  pure1 ()

main1 : IO ()
main1 = run $ do
  MkAllocated ptr  <- new 0
  lock <- mkLock [ptr] IsEven (0 ** Refl)
  (() # ()) <- par1
    (printAndUpdate "A" ? (plus2Even . squaredEven) lock)
    (printAndUpdate "B" ? (squaredEven . plus2Even) lock)
  pure ()


------------------------------------------------------------------------
-- Example: concurrent programs manipulating two cells summing to 10

SumToTen : Predicate [Nat, Nat]
SumToTen m n = m + n === 10

swapSumToTen : SumToTen m n -> SumToTen n m
swapSumToTen prf = trans (plusCommutative n m) prf

decrSumToTen : SumToTen (S m) n -> SumToTen m (S n)
decrSumToTen prf = trans (sym $ plusSuccRightSucc m n) prf

decrOrSwap : Nat -> Nat -> (Nat, Nat)
decrOrSwap Z n = (n, Z)
decrOrSwap (S m) n = (m, S n)

decrOrSwapSumToTen : {m : Nat} -> SumToTen m n -> SumToTen (fst (decrOrSwap m n)) (snd (decrOrSwap m n))
decrOrSwapSumToTen {m = Z} prf = swapSumToTen prf
decrOrSwapSumToTen {m = S m} prf = trans (sym $ plusSuccRightSucc m n) prf

export
printAndUpdates :
  String ->
  (f : Nat -> Nat -> (Nat, Nat)) ->
  (0 prfF : forall m, n. SumToTen m n -> SumToTen (fst (f m n)) (snd (f m n))) ->
  Lock [c, d] SumToTen -> L1 IO ()
printAndUpdates identity f prfF l = do
  randomSleep identity
  withLock l $ \ ([ptr1, ptr2] # prf) => do
    putStrLn "\{identity}: lock acquired"
    ((ptr1 # Val m) # (ptr2 # Val n)) <-
        par1 (get (identity ++ "1") ptr1)
             (get (identity ++ "2") ptr2)
    (ptr1 # ptr2) <-
        par1 (put (identity ++ "1") ptr1 (fst (f m n)))
             (put (identity ++ "2") ptr2 (snd (f m n)))
    pure1 (([ptr1, ptr2] # prfF prf) # ())
  putStrLn "\{identity}: lock released"
  pure1 ()


main2 : IO ()
main2 = run $ do
  MkAllocated ptr1 <- new 2
  MkAllocated ptr2 <- new 8
  lock <- mkLock [ptr1, ptr2] SumToTen Refl
  (() # ()) <- par1
    (printAndUpdates "A" (\ m, n => (n, m)) swapSumToTen lock)
    (printAndUpdates "B" ? decrOrSwapSumToTen lock)
  pure ()
