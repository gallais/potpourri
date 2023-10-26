module MultiChannel

import Decidable.Equality
import Data.Vect


import Control.Linear.LIO
import Control.Linear.Network
import Data.Linear.Bifunctor
import Data.Linear.LVect
import Data.Linear.Notation

%default total

------------------------------------------------------------------------
-- This is, modulo argument order, punchOut in Agda's stdlib

adjust : (c, k : Fin (S n)) -> Not (c === k) -> Fin n
adjust FZ FZ neq = absurd (neq Refl)
adjust FZ (FS FZ) neq = FZ
adjust FZ (FS (FS _)) neq = FZ
adjust (FS c) FZ neq = c
adjust (FS c) (FS FZ) neq = FS (adjust c FZ (\ eq => neq (cong FS eq)))
adjust (FS c) (FS k@(FS _)) neq = FS (adjust c k (\ eq => neq (cong FS eq)))

------------------------------------------------------------------------
-- Split m n r is a proof that
-- r can be obtained
-- by interleaving m and n

data Split : (m, n, r : Nat) -> Type where
  Null  : Split 0 0 0
  Left  : Split m n r -> Split (S m) n (S r)
  Right : Split m n r -> Split m (S n) (S r)

%name Split sp

applySplit : Split m n r -> Vect r a -> (Vect m a, Vect n a)
applySplit Null xs = ([], [])
applySplit (Left sp) (x :: xs) = mapFst (x ::) (applySplit sp xs)
applySplit (Right sp) (x :: xs) = mapSnd (x ::) (applySplit sp xs)

locateSplit : Split m n r -> Fin r -> Either (Fin m) (Fin n)
locateSplit (Left sp) FZ = Left FZ
locateSplit (Left sp) (FS k) = mapFst FS (locateSplit sp k)
locateSplit (Right sp) FZ = Right FZ
locateSplit (Right sp) (FS k) = mapSnd FS (locateSplit sp k)

------------------------------------------------------------------------
-- Input/Output directions

namespace Direction

  public export
  data Direction = INP | OUT

  %name Direction d

  public export
  dual : Direction -> Direction
  dual INP = OUT
  dual OUT = INP

------------------------------------------------------------------------
-- Base types carried by channels

data Ty = TyInt | TyBool

%name Ty ty

Meaning : Ty -> Type
Meaning TyInt = Integer
Meaning TyBool = Bool

------------------------------------------------------------------------
-- Sessions are obtained by projecting a multi-party session
-- according to a channel

namespace Session

  public export
  data Session : Type where
    Transmit : Direction -> Ty ->  Session -> Session
    Delegate : Direction -> Session -> Session -> Session
    Branch : Direction -> Session -> Session -> Session
    End : Session

  %name Session s, t

  public export
  dual : Session -> Session
  dual (Transmit d ty s) = Transmit (dual d) ty (dual s)
  dual (Delegate d s t) = Delegate (dual d) s (dual t)
  dual (Branch d s t) = Branch (dual d) (dual s) (dual t)
  dual End = End

------------------------------------------------------------------------
-- Multi-session types, indexed by the number of channels

data MSession : Nat -> Type
0 Causality : Fin n -> MSession n -> MSession n -> Type
CheckDual0 : MSession (S m) -> MSession (S n) -> Type


data MSession : Nat -> Type where
  Transmit : Direction -> Fin n -> Ty -> MSession n -> MSession n
  Branch   : Direction -> (c : Fin n) -> (m1, m2 : MSession n) ->
             Causality c m1 m2 -> MSession n
  Close : Fin (S n) -> MSession n -> MSession (S n)
  Terminate : MSession 0
  Connect : Split m n r ->
            (m1 : MSession (S m)) ->
            (m2 : MSession (S n)) ->
            CheckDual0 m1 m2 -> -- new channel called FZ on both sides
            MSession r
  DelegateOut : (c, j : Fin (S n)) -> Not (c === j) -> Session -> MSession n -> MSession (S n)
  DelegateIn : (c : Fin n) -> MSession (S n) -> MSession n

%name MSession s, t

project : Fin n -> MSession n -> Session
project c (Transmit d x ty s) with (decEq c x)
  _ | Yes pr = Transmit d ty (project c s)
  _ | No npr = project c s
project c (Branch d x m1 m2 causal) with (decEq c x)
  _ | Yes pr = Branch d (project c m1) (project c m2)
  _ | No npr = project c m1
project c (Close x s) with (decEq c x)
  _ | Yes pr = End
  _ | No npr = project (adjust c x npr) s
project c (Connect sp m1 m2 x) with (locateSplit sp c)
  _ | Left c' = project (FS c') m1
  _ | Right c' = project (FS c') m2
project c (DelegateOut x j neq sj t) with (decEq c x)
  _ | Yes pr1 = Delegate OUT sj (project (adjust c j (\ eq => neq (trans (sym pr1) eq))) t)
  _ | No npr1 with (decEq c j)
    _ | Yes pr2 = sj
    _ | No npr2 = project (adjust c j npr2) t
project c (DelegateIn x s) with (decEq c x)
  _ | Yes pr = Delegate INP (project FZ s) (project (FS c) s)
  _ | No npr = project (FS c) s

Causality i m1 m2 = (j : Fin _) -> Not (i === j) -> project j m1 === project j m2

CheckDual0 m1 m2 = project FZ m1 === dual (project FZ m2)

------------------------------------------------------------------------
-- Commands indexed by the session type they respect

data Cmd : (r, a : Type) -> (n : Nat) -> MSession n -> Type where
  CLOSE  : (c : Fin (S n)) -> (a -@ b) -> Cmd r b n s -> Cmd r a (S n) (Close c s)
  SEND   : {ty : Ty} -> (c : Fin n) ->
           (a -@ LPair (Meaning ty) b) ->
           Cmd r b n s -> Cmd r a n (Transmit OUT c ty s)
  RECV   : (c : Fin n) -> (Meaning ty -> a -> b) -> Cmd r b n s -> Cmd r a n (Transmit INP c ty s)
  SELECT : {0 f : Bool -> Type} -> (c : Fin n) -> (causal : Causality c m1 m2) -> (a -> (b : Bool ** f b))
    -> Cmd r (f true) n m1 -> Cmd r (f false) n m2 -> Cmd r a n (Branch OUT c m1 m2 causal)
  CHOICE : (c : Fin n) -> (causal : Causality c m1 m2)
    -> Cmd r a n m1 -> Cmd r a n m2 -> Cmd r a n (Branch INP c m1 m2 causal)
  CONNECT : (check : CheckDual0 m1 m2)
    -> (split : a -> (a1, a2))
    -> (sp : Split m n p)
    -> Cmd r a1 (S m) m1 -> Cmd r a2 (S n) m2
    -> Cmd r a p (Connect sp m1 m2 check)
  SENDCH : (c, j : Fin (S n)) -> (neq : Not (c === j))
    -> Cmd r a n s -> Cmd r a (S n) (DelegateOut c j neq sj s)
  RECVCH : (c : Fin n) -> Cmd r a (S n) s -> Cmd r a n (DelegateIn c s)
  END    : (a -> r) -> Cmd r a 0 terminate

------------------------------------------------------------------------

finNonZeroNat : (c : Fin n) -> n === S (pred n)
finNonZeroNat FZ = Refl
finNonZeroNat (FS k) = Refl

actOn : LinearIO io
     => Fin n
     -> LVect n (Socket Open)
     -@ (Socket Open -@ L1 io (LPair a (Socket Open)))
     -@ L1 io (LPair a (LVect n (Socket Open)))
actOn c = go c (finNonZeroNat c) where

  go : {0 m, n : Nat} -> Fin n -> (0 _ : n === S m)
    -> LVect n (Socket Open)
    -@ (Socket Open -@ L1 io (LPair a (Socket Open)))
    -@ L1 io (LPair a (LVect n (Socket Open)))
  go c Refl sks k = do
    (sk # sks) <- pure1 (lookup c sks)
    (v # sk) <- k sk
    sks <- pure1 (insertAt c sk sks)
    pure1 (v # sks)

serialise : {ty : Ty} -> Meaning ty -@ !* String
serialise {ty = TyInt} v = let str = assert_linear show v in MkBang str
serialise {ty = TyBool} v = ?a_1

exec : LinearIO io
    => Cmd r a n s
    -@ a
    -@ LVect n (Socket Open)
    -@ L1 io r
exec (CLOSE c f s) a sks = do
  (sk # sks) <- pure1 (lookup c sks)
  sk <- close sk
  done sk
  exec s (f a) sks
exec (SEND {ty} c f s) a sks = do
  (x # b) <- pure1 (f a)
  (() # sks) <- actOn c sks $ \ sk => do
    MkBang str <- pure1 (serialise x)
    (Nothing # sk) <- send sk str
      | (Just err # sk) => done sk >> assert_total (idris_crash "oops")
    pure1 (() # sk)
  exec s b sks
exec (RECV c f x) a sks = ?a_2
exec (SELECT c causal f x y) a sks = ?a_3
exec (CHOICE c causal x y) a sks = ?a_4
exec (CONNECT check split sp x y) a sks = ?a_5
exec (SENDCH c j neq x) a sks = ?a_6
exec (RECVCH c x) a sks = ?a_7
exec (END f) a sks = ?a_8
