module System.Concurrency.Session.Recursive2

import Control.Linear.LIO

import Data.List.AtIndex
import Data.Nat

import Data.OpenUnion
import System
import System.File
import System.Concurrency as Threads
import System.Concurrency.Linear

import Language.Reflection

%default total

------------------------------------------------------------------------
-- Session types

namespace Session

  public export
  data Kind = Open | Closed

  public export
  data Norm = Head | Expr

  ||| A session type describes the interactions one thread may have with
  ||| another over a shared bidirectional channel: it may send or receive
  ||| values of arbitrary types, or be done communicating.
  public export
  data Session : Kind -> Norm -> Type where
    -- Recursive parts
    Fix  : (s : Session Open Head) -> Session Closed Expr
    Rec  : Session Open Expr
    -- Usual operations
    Send : (ty : Type) -> (s : Session k n) -> Session k Head
    Recv : (ty : Type) -> (s : Session k n) -> Session k Head
    End  : Session k Head

  ||| Dual describes how the other party to the communication sees the
  ||| interactions: our sends become their receives and vice-versa.
  public export
  Dual : Session k m -> Session k m
  Dual (Fix s) = Fix (Dual s)
  Dual Rec = Rec
  Dual (Send ty s) = Recv ty (Dual s)
  Dual (Recv ty s) = Send ty (Dual s)
  Dual End = End

  ||| Duality is involutive: the dual of my dual is me
  export
  dualInvolutive : (s : Session k m) -> Dual (Dual s) === s
  dualInvolutive (Fix s) = cong Fix (dualInvolutive s)
  dualInvolutive Rec = Refl
  dualInvolutive (Send ty s) = cong (Send ty) (dualInvolutive s)
  dualInvolutive (Recv ty s) = cong (Recv ty) (dualInvolutive s)
  dualInvolutive End = Refl

  export
  plug : Session Closed Expr -> Session Open m -> Session Closed m
  plug t Rec = t
  plug t (Send ty s) = Send ty (plug t s)
  plug t (Recv ty s) = Recv ty (plug t s)
  plug t End = End

  ||| Head normalise a session to expose a constructor
  export
  norm : Session Closed m -> Session Closed Head
  norm t@(Fix s) = plug t s
  norm t@(Send ty s) = t
  norm t@(Recv ty s) = t
  norm t@End = t

||| We can collect the list of types that will be sent over the
||| course of a session by walking down its description
||| This definition is purely internal and will not show up in
||| the library's interface.
SendTypes : Session k m -> List Type
SendTypes (Fix s) = SendTypes s
SendTypes Rec = []
SendTypes (Send ty s) = ty :: SendTypes s
SendTypes (Recv ty s) = SendTypes s
SendTypes End = []

||| We can collect the list of types that will be received over
||| the course of a session by walking down its description
||| This definition is purely internal and will not show up in
||| the library's interface.
RecvTypes : Session k m -> List Type
RecvTypes (Fix s) = RecvTypes s
RecvTypes Rec = []
RecvTypes (Send ty s) = RecvTypes s
RecvTypes (Recv ty s) = ty :: RecvTypes s
RecvTypes End = []

||| The types received by my dual are exactly the ones I am sending
||| This definition is purely internal and will not show up in
||| the library's interface.
RecvDualTypes : (s : Session k m) -> RecvTypes (Dual s) === SendTypes s
RecvDualTypes (Fix s) = RecvDualTypes s
RecvDualTypes Rec = Refl
RecvDualTypes (Send ty s) = cong (ty ::) (RecvDualTypes s)
RecvDualTypes (Recv ty s) = RecvDualTypes s
RecvDualTypes End = Refl

||| The types sent by my dual are exactly the ones I receive
||| This definition is purely internal and will not show up in
||| the library's interface.
SendDualTypes : (s : Session k m) -> SendTypes (Dual s) === RecvTypes s
SendDualTypes (Fix s) = SendDualTypes s
SendDualTypes Rec = Refl
SendDualTypes (Send ty s) = SendDualTypes s
SendDualTypes (Recv ty s) = cong (ty ::) (SendDualTypes s)
SendDualTypes End = Refl

namespace Headed

  public export
  data Headed : Nat -> Nat -> Session m1 Head -> Session m2 k2 -> Type where
    Recv : (ty : Type) -> {s : Session m2 k2} -> Headed 1 0 (Recv ty s) s
    Send : (ty : Type) -> {s : Session m2 k2} -> Headed 0 1 (Send ty s) s

namespace Prefix

  public export
  data Prefix : Nat -> Nat -> Session m1 Head -> Session m2 k2 -> Type where
    Lin  : Prefix 0 0 s s
    (:<) : Prefix p q s s' -> Headed m n s' s'' -> Prefix (p + m) (q + n) s s''

namespace Loop

  public export
  data Loop : Session Open Head -> Nat -> Nat -> Session m2 k2 -> Type where
    Lin  : Loop o 0 0 o
    (:<) : Loop o p q s' -> Headed m n s' s'' -> Loop o (p + m) (q + n) s''

data Env : Kind -> Type where
  Nothing : Env Closed
  Just    : Session Open Head -> Env Open

public export
data Context : Nat -> Nat -> Session Closed Head -> Session m2 k2 -> Env m2 -> Type where
  InPrefix : (0 _ : Prefix p q s s') ->
             Context p q s s' Nothing
  Pumping  : {p, q : Nat} -> (0 _ : Prefix p q s (Fix o)) -> (0 _ : Loop o m n s') ->
             Context (p + m) (q + n) s s' (Just o)

export
record Channel (s : Session m2 k2) (e : Env m2) where
  constructor MkChannel
  {sendStep    : Nat}
  {recvStep    : Nat}
  {0 ogSession : Session Closed Head}
  context      : Context recvStep sendStep ogSession s e

  sendChan : Threads.Channel (Union (SendTypes ogSession))
  recvChan : Threads.Channel (Union (RecvTypes ogSession))

recvHeaded :
  Headed m n s s' ->
  AtIndex ty (RecvTypes s') i ->
  AtIndex ty (RecvTypes s) (m + i)
recvHeaded (Recv _) idx = S idx
recvHeaded (Send _) idx = idx

recvPrefix :
  Prefix m n start s ->
  AtIndex ty (RecvTypes s) i ->
  AtIndex ty (RecvTypes start) (m + i)
recvPrefix [<] idx = idx
recvPrefix ((:<) {m, p} pref s) idx
  = rewrite sym $ plusAssociative p m i in
    recvPrefix pref (recvHeaded s idx)

recvLoop :
  Loop o m n s ->
  AtIndex ty (RecvTypes s) i ->
  AtIndex ty (RecvTypes o) (m + i)
recvLoop [<] idx = idx
recvLoop ((:<) {p, m} loop s) idx
  = rewrite sym $ plusAssociative p m i in
    recvLoop loop (recvHeaded s idx)

0 recvContext :
  Context m n start s e ->
  AtIndex ty (RecvTypes s) i ->
  AtIndex ty (RecvTypes start) (m + i)
recvContext (InPrefix pref) idx = recvPrefix pref idx
recvContext (Pumping {p, m} pref loop) idx
  = rewrite sym $ plusAssociative p m i in
    recvPrefix pref (recvLoop loop idx)

Recv :
  (0 ty : Type) ->
  Context m n s (Recv ty s') e ->
  Context (S m) n s s' e
Recv ty (InPrefix pref)
  = rewrite plusCommutative 1 m in
    rewrite plusCommutative 0 n in
    InPrefix (pref :< Recv ty)
Recv ty (Pumping {p, q, m, n} pref loop)
  = rewrite plusSuccRightSucc p m in
    rewrite plusCommutative 1 m in
    rewrite plusCommutative 0 n in
    Pumping pref (loop :< Recv ty)

Enter :
  {m, n : Nat} ->
  Context m n s (Fix o) e ->
  Context m n s o (Just o)
Enter (InPrefix pref)
  = rewrite plusCommutative 0 m in
    rewrite plusCommutative 0 n in
    Pumping pref [<]

Unfold :
  Context m n s Rec (Just o) ->
  (m : Nat ** n : Nat ** Context m n s o (Just o))
Unfold (Pumping {p, q} pref loop)
  = MkDPair p
  $ MkDPair q
  $ rewrite plusCommutative 0 p in
    rewrite plusCommutative 0 q in
    Pumping pref [<]

Fold :
  Context m n s Rec (Just o) ->
  (m : Nat ** n : Nat ** Context m n s (Fix o) Nothing)
Fold (Pumping {p, q} pref loop)
  = MkDPair p
  $ MkDPair q
  $ InPrefix pref

export
recv : LinearIO io =>
  Channel (Recv ty s) e -@
  L1 io (Res ty (const (Channel s e)))
recv (MkChannel {recvStep} ctxt sendCh recvCh) = do
  x@(Element k prf val) <- channelGet recvCh
  -- Here we check that we got the right message by projecting out of
  -- the union type using the current `recvStep`. Both ends should be
  -- in sync because of the `RecvDualTypes` and `SendDualTypes` lemmas.
  let Just val = prj (recvStep + 0) (recvContext ctxt Z) x
    | Nothing => die1 "Error: invalid recv expected \{show recvStep} but got \{show k}"
  pure1 (val # MkChannel (Recv ty ctxt) sendCh recvCh)

export
enter : LinearIO io =>
  Channel (Fix s) e -@
  L1 io (Channel s (Just s))
enter (MkChannel ctxt sendCh recvCh) = do
  pure1 (MkChannel (Enter ctxt) sendCh recvCh)

export
unfold : LinearIO io =>
  Channel Rec (Just s) -@
  L1 io (Channel s (Just s))
unfold (MkChannel ctxt sendCh recvCh) = do
  let (p ** q ** ctxt) = Unfold ctxt
  pure1 (MkChannel ctxt sendCh recvCh)

export
fold : LinearIO io =>
  Channel Rec (Just s) -@
  L1 io (Channel (Fix s) Nothing)
fold (MkChannel ctxt sendCh recvCh) = do
  let (p ** q ** ctxt) = Fold ctxt
  pure1 (MkChannel ctxt sendCh recvCh)

NatsSession : Session ? ?
NatsSession = Fix (Recv Nat Rec)

covering export
getNats : LinearIO io =>
  (1 _ : Channel NatsSession Nothing) -> L1 io ()
getNats ch = do
  ch <- enter ch
  (n # ch) <- recv ch
  ch <- fold ch
  getNats ch
