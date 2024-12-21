module System.Concurrency.Session.Recursive

import Control.Linear.LIO

import Data.DPair
import Data.List.HasLength
import Data.List.AtIndex
import Data.Nat

import Data.OpenUnion
import System
import System.File
import System.Concurrency as Threads
import System.Concurrency.Linear

import Language.Reflection

%default total


interface Logging io where
  logging : LinearIO io => String -> L io ()

[LOG] Logging io where
  logging = putStrLn
[QUIET] Logging io where
  logging str = pure ()

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
    Fix : (s : Session Open Head) -> Session Closed Expr
    Rec : Session Open Expr
    -- Usual operations
    Send : (ty : Type) -> (s : Session k n) -> Session k Head
    Recv : (ty : Type) -> (s : Session k n) -> Session k Head
    -- End a session
    End : Session k Head
    -- Choice
    Offer : (s : Session k m1) -> (t : Session k m2) -> Session k Head
    Select : (s : Session k m1) -> (t : Session k m2) -> Session k Head

  ||| Dual describes how the other party to the communication sees the
  ||| interactions: our sends become their receives and vice-versa.
  public export
  Dual : Session k m -> Session k m
  Dual (Fix s) = Fix (Dual s)
  Dual Rec = Rec
  Dual (Send ty s) = Recv ty (Dual s)
  Dual (Recv ty s) = Send ty (Dual s)
  Dual End = End
  Dual (Offer s t) = Select (Dual s) (Dual t)
  Dual (Select s t) = Offer (Dual s) (Dual t)

  ||| Duality is involutive: the dual of my dual is me
  export
  dualInvolutive : (s : Session k m) -> Dual (Dual s) === s
  dualInvolutive (Fix s) = cong Fix (dualInvolutive s)
  dualInvolutive Rec = Refl
  dualInvolutive (Send ty s) = cong (Send ty) (dualInvolutive s)
  dualInvolutive (Recv ty s) = cong (Recv ty) (dualInvolutive s)
  dualInvolutive End = Refl
  dualInvolutive (Offer s t) = cong2 Offer (dualInvolutive s) (dualInvolutive t)
  dualInvolutive (Select s t) = cong2 Select (dualInvolutive s) (dualInvolutive t)

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
SendTypes (Offer s1 s2) = SendTypes s1 ++ SendTypes s2
SendTypes (Select s1 s2) = SendTypes s1 ++ SendTypes s2

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
RecvTypes (Offer s1 s2) = RecvTypes s1 ++ RecvTypes s2
RecvTypes (Select s1 s2) = RecvTypes s1 ++ RecvTypes s2



||| The types received by my dual are exactly the ones I am sending
||| This definition is purely internal and will not show up in
||| the library's interface.
RecvDualTypes : (s : Session k m) -> RecvTypes (Dual s) === SendTypes s
RecvDualTypes (Fix s) = RecvDualTypes s
RecvDualTypes Rec = Refl
RecvDualTypes (Send ty s) = cong (ty ::) (RecvDualTypes s)
RecvDualTypes (Recv ty s) = RecvDualTypes s
RecvDualTypes End = Refl
RecvDualTypes (Offer s1 s2) = cong2 (++) (RecvDualTypes s1) (RecvDualTypes s2)
RecvDualTypes (Select s1 s2) = cong2 (++) (RecvDualTypes s1) (RecvDualTypes s2)

||| The types sent by my dual are exactly the ones I receive
||| This definition is purely internal and will not show up in
||| the library's interface.
SendDualTypes : (s : Session k m) -> SendTypes (Dual s) === RecvTypes s
SendDualTypes (Fix s) = SendDualTypes s
SendDualTypes Rec = Refl
SendDualTypes (Send ty s) = SendDualTypes s
SendDualTypes (Recv ty s) = cong (ty ::) (SendDualTypes s)
SendDualTypes End = Refl
SendDualTypes (Offer s1 s2) = cong2 (++) (SendDualTypes s1) (SendDualTypes s2)
SendDualTypes (Select s1 s2) = cong2 (++) (SendDualTypes s1) (SendDualTypes s2)

namespace Headed

  public export
  data Headed : Nat -> Nat -> Session m1 Head -> Session m2 k2 -> Type where
    Recv    : (ty : Type) -> {s : Session m2 k2} -> Headed 1 0 (Recv ty s) s
    Send    : (ty : Type) -> {s : Session m2 k2} -> Headed 0 1 (Send ty s) s
    OfferL  : {s1, s2 : _} -> Headed 0 0 (Offer s1 s2) s1
    OfferR  : {s1, s2 : _} -> Headed (length (RecvTypes s1)) (length (SendTypes s1)) (Offer s1 s2) s2
    SelectL : {s1, s2 : _} -> Headed 0 0 (Select s1 s2) s1
    SelectR : {s1, s2 : _} -> Headed (length (RecvTypes s1)) (length (SendTypes s1)) (Select s1 s2) s2

namespace Prefix

  public export
  data Prefix : Nat -> Nat -> Session m1 k1 -> Session m2 k2 -> Type where
    Lin  : Prefix 0 0 s s
    (:<) : Prefix p q s s' -> Headed m n s' s'' -> Prefix (p + m) (q + n) s s''

  public export infixl 6 :<!

  export
  (:<!) : Prefix p q s s' -> Headed m n s' s'' -> Prefix (m + p) (n + q) s s''
  pref :<! hd
    = rewrite plusCommutative m p in
      rewrite plusCommutative n q in
      pref :< hd

namespace Loop

  public export
  data Loop : Session Open Head -> Nat -> Nat -> Session m2 k2 -> Type where
    Lin  : Loop o 0 0 o
    (:<) : Loop o p q s' -> Headed m n s' s'' -> Loop o (p + m) (q + n) s''

  export
  (:<!) : Loop o p q s' -> Headed m n s' s'' -> Loop o (m + p) (n + q) s''
  pref :<! hd
    = rewrite plusCommutative m p in
      rewrite plusCommutative n q in
      pref :< hd

data Env : Kind -> Type where
  Nothing : Env Closed
  Just    : Session Open Head -> Env Open

public export
data Context : Nat -> Nat -> Session m1 k1 -> Session m2 k2 -> Env m2 -> Type where
  InPrefix : {p, q : Nat} -> (0 _ : Prefix p q s s') ->
             Context p q s s' Nothing
  Pumping  : {m, n, p, q : Nat} -> (0 _ : Prefix p q s (Fix o)) -> (0 _ : Loop o m n s') ->
             Context (p + m) (q + n) s s' (Just o)

export
record Channel (me, them : String) (s : Session m2 k2) (e : Env m2) where
  constructor MkChannel
  {sendStep    : Nat}
  {recvStep    : Nat}
  {0 ogNorm    : Norm}
  {0 ogKind    : Kind}
  {0 ogSession : Session ogKind ogNorm}
  context      : Context recvStep sendStep ogSession s e

  -- we throw in Bool for Offer & Select
  sendChan : Threads.Channel (Union (Bool :: SendTypes ogSession))
  recvChan : Threads.Channel (Union (Bool :: RecvTypes ogSession))


0 recvHeaded :
  Headed m n s s' ->
  AtIndex ty (RecvTypes s') i ->
  AtIndex ty (RecvTypes s) (m + i)
recvHeaded (Recv _) idx = S idx
recvHeaded (Send _) idx = idx
recvHeaded OfferL idx = weakenR idx
recvHeaded (OfferR {s1, s2}) idx
  = weakenL (Element _ (hasLength _)) idx
recvHeaded SelectL idx = weakenR idx
recvHeaded (SelectR {s1, s2}) idx
  = weakenL (Element _ (hasLength _)) idx

0 recvPrefix :
  Prefix m n start s ->
  AtIndex ty (RecvTypes s) i ->
  AtIndex ty (RecvTypes start) (m + i)
recvPrefix [<] idx = idx
recvPrefix ((:<) {m, p} pref s) idx
  = rewrite sym $ plusAssociative p m i in
    recvPrefix pref (recvHeaded s idx)

0 recvLoop :
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
  = InPrefix (pref :<! Recv ty)
Recv ty (Pumping {p, q, m, n} pref loop)
  = rewrite plusSuccRightSucc p m in
    Pumping pref (loop :<! Recv ty)

sendHeaded :
  Headed m n s s' ->
  AtIndex ty (SendTypes s') i ->
  AtIndex ty (SendTypes s) (n + i)
sendHeaded (Recv _) idx = idx
sendHeaded (Send _) idx = S idx
sendHeaded OfferL idx = weakenR idx
sendHeaded (OfferR {s1, s2}) idx
  = weakenL (Element _ (hasLength _)) idx
sendHeaded SelectL idx = weakenR idx
sendHeaded (SelectR {s1, s2}) idx
  = weakenL (Element _ (hasLength _)) idx


sendPrefix :
  Prefix m n start s ->
  AtIndex ty (SendTypes s) i ->
  AtIndex ty (SendTypes start) (n + i)
sendPrefix [<] idx = idx
sendPrefix ((:<) {n, q} pref s) idx
  = rewrite sym $ plusAssociative q n i in
    sendPrefix pref (sendHeaded s idx)

sendLoop :
  Loop o m n s ->
  AtIndex ty (SendTypes s) i ->
  AtIndex ty (SendTypes o) (n + i)
sendLoop [<] idx = idx
sendLoop ((:<) {q, n} loop s) idx
  = rewrite sym $ plusAssociative q n i in
    sendLoop loop (sendHeaded s idx)

0 sendContext :
  Context m n start s e ->
  AtIndex ty (SendTypes s) i ->
  AtIndex ty (SendTypes start) (n + i)
sendContext (InPrefix pref) idx = sendPrefix pref idx
sendContext (Pumping {q, n} pref loop) idx
  = rewrite sym $ plusAssociative q n i in
    sendPrefix pref (sendLoop loop idx)

Send :
  (0 ty : Type) ->
  Context m n s (Send ty s') e ->
  Context m (S n) s s' e
Send ty (InPrefix pref)
  = InPrefix (pref :<! Send ty)
Send ty (Pumping {p, q, m, n} pref loop)
  = rewrite plusSuccRightSucc q n in
    Pumping pref (loop :<! Send ty)

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
recv : Logging io => Show ty => LinearIO io =>
  {me : String} ->
  Channel me them (Recv ty s) e -@
  L1 io (Res ty (const (Channel me them s e)))
recv (MkChannel {recvStep} ctxt sendCh recvCh) = do
  x@(Element k prf val) <- channelGet recvCh
  -- Here we check that we got the right message by projecting out of
  -- the union type using the current `recvStep`. Both ends should be
  -- in sync because of the `RecvDualTypes` and `SendDualTypes` lemmas.
  let Just val = prj (S recvStep) (rewrite plusCommutative 0 recvStep in S (recvContext ctxt Z)) x
    | Nothing => die1 "Error: invalid recv expected \{show recvStep} but got \{show k}"
  logging "\{me} just received \{show val} (at index \{show k})"
  pure1 (val # MkChannel (Recv ty ctxt) sendCh recvCh)

OfferL :
  Context m n s (Offer s1 s2) e ->
  Context m n s s1 e
OfferL (InPrefix pref) = InPrefix (pref :<! OfferL)
OfferL (Pumping pref loop) = Pumping pref (loop :<! OfferL)

OfferR :
  {s1 : _} ->
  Context m n s (Offer s1 s2) e ->
  (m : Nat ** n : Nat ** Context m n s s2 e)
OfferR (InPrefix pref) = (_ ** _ ** InPrefix (pref :<! OfferR))
OfferR (Pumping pref loop) = (_ ** _ ** Pumping pref (loop :<! OfferR))

export
offer : LinearIO io =>
  {s1, s2 : _} ->
  Channel me them (Offer s1 s2) e -@
  L1 io (Res Bool $ \ b => ifThenElse b (Channel me them s1 e) (Channel me them s2 e))
offer (MkChannel ctxt sendCh recvCh) = do
  x@(Element idx prf val) <- channelGet recvCh
  -- Here we check that we got the right message by projecting out of
  -- the union type using the current `recvStep`. Both ends should be
  -- in sync because of the `RecvDualTypes` and `SendDualTypes` lemmas.
  let Just val = prj 0 Z x
    | Nothing => do
      die1 "Error: invalid recv expected (Offer selection) but got \{show idx}"
  pure1 $ val # if val
    then MkChannel (OfferL ctxt) sendCh recvCh
    else let (_ ** _ ** ctxt) = OfferR ctxt in MkChannel ctxt sendCh recvCh

SelectL :
  Context m n s (Select s1 s2) e ->
  Context m n s s1 e
SelectL (InPrefix pref) = InPrefix (pref :<! SelectL)
SelectL (Pumping pref loop) = Pumping pref (loop :<! SelectL)

SelectR :
  {s1 : _} ->
  Context m n s (Select s1 s2) e ->
  (m : Nat ** n : Nat ** Context m n s s2 e)
SelectR (InPrefix pref) = (_ ** _ ** InPrefix (pref :<! SelectR))
SelectR (Pumping pref loop) = (_ ** _ ** Pumping pref (loop :<! SelectR))

export
select : LinearIO io =>
  {s1, s2 : _} ->
  (1 ch : Channel me them (Select s1 s2) e) ->
  (b : Bool) ->
  L1 io (ifThenElse b (Channel me them s1 e) (Channel me them s2 e))
select (MkChannel ctxt sendCh recvCh) b = do
  let val = inj 0 Z b
  channelPut sendCh val
  -- Here we check that we got the right message by projecting out of
  -- the union type using the current `recvStep`. Both ends should be
  -- in sync because of the `RecvDualTypes` and `SendDualTypes` lemmas.
  pure1 $ if b
    then MkChannel (SelectL ctxt) sendCh recvCh
    else let (_ ** _ ** ctxt) := SelectR ctxt in MkChannel ctxt sendCh recvCh

export
send : Logging io => Show ty => LinearIO io =>
  {me : String} ->
  (1 _ : Channel me them (Send ty s) e) ->
  ty ->
  L1 io (Channel me them s e)
send (MkChannel {sendStep} ctxt sendCh recvCh) v = do
  let val = inj (S sendStep) (rewrite plusCommutative 0 sendStep in S (sendContext ctxt Z)) v
  channelPut sendCh val
  logging "\{me} just sent \{show v} (at index \{show (1+ sendStep)})"
  -- Here we check that we got the right message by projecting out of
  -- the union type using the current `recvStep`. Both ends should be
  -- in sync because of the `RecvDualTypes` and `SendDualTypes` lemmas.
  pure1 (MkChannel (Send ty ctxt) sendCh recvCh)

export
enter : LinearIO io =>
  Channel me them (Fix s) e -@
  L1 io (Channel me them s (Just s))
enter (MkChannel ctxt sendCh recvCh) = do
  pure1 (MkChannel (Enter ctxt) sendCh recvCh)

export
unfold : LinearIO io =>
  Channel me them Rec (Just s) -@
  L1 io (Channel me them s (Just s))
unfold (MkChannel ctxt sendCh recvCh) = do
  let (p ** q ** ctxt) = Unfold ctxt
  pure1 (MkChannel ctxt sendCh recvCh)

export
fold : LinearIO io =>
  Channel me them Rec (Just s) -@
  L1 io (Channel me them (Fix s) Nothing)
fold (MkChannel ctxt sendCh recvCh) = do
  let (p ** q ** ctxt) = Fold ctxt
  pure1 (MkChannel ctxt sendCh recvCh)

export
close : LinearIO io =>
  Channel me them End e -@
  L io ()
close (MkChannel{}) = pure ()

||| Given a session, create a bidirectional communiaction channel and
||| return its two endpoints
export
makeChannel :
  LinearIO io =>
  (0 s : Session Closed m) ->
  L1 io (LPair (Channel me them s Nothing) (Channel them me (Dual s) Nothing))
makeChannel s = do
  sendChan <- Threads.makeChannel
  recvChan <- Threads.makeChannel
  let 1 posCh : Channel me them s Nothing
    := MkChannel (InPrefix [<]) sendChan recvChan
  let 1 negCh : Channel them me (Dual s) Nothing
    := MkChannel (InPrefix [<])
         (rewrite SendDualTypes s in recvChan)
         (rewrite RecvDualTypes s in sendChan)
  pure1 (posCh # negCh)


||| Given a session and two functions communicating according to that
||| sesion, we can run the two programs concurrently and collect their
||| final results.
||| The `src` and `tgt` names are purely for logging purposes.
export
fork : (0 s : Session Closed m) ->
       (me, them : String) ->
       (Channel me them s        Nothing -@ L IO a) -@
       (Channel them me (Dual s) Nothing -@ L IO b) -@
       L IO (a, b)
fork s me them kA kB = do
  (posCh # negCh) <- Recursive.makeChannel s
  -- Forked threads cannot return anything so we grab a couple of
  -- low-level channels just to get the results back out
  aResChan <- Threads.makeChannel
  bResChan <- Threads.makeChannel
  -- Fork the two processes, send the results back along the appropriate channel
  _ <- liftIO1 $ IO.fork $ LIO.run $ kA posCh >>= channelPut aResChan
  _ <- liftIO1 $ IO.fork $ LIO.run $ kB negCh >>= channelPut bResChan
  -- Wait for both to finish and send their results
  x <- channelGet aResChan
  y <- channelGet bResChan
  pure (x, y)


------------------------------------------------------------------------
-- Example
------------------------------------------------------------------------

Sum : Session Closed Expr
Sum = Fix (Select (Recv Nat End) $ Send Nat Rec)

sumNats : Logging io => LinearIO io => {me : String} ->
  List Nat -> -- list of arguments
  Channel me them Sum Nothing -@ L io Nat
sumNats [] ch = do
  ch <- enter ch
  ch <- select ch True
  (n # ch) <- recv ch
  close ch
  pure n
sumNats (n :: ns) ch = do
  ch <- enter ch
  ch <- select ch False
  ch <- send ch n
  ch <- fold ch
  sumNats ns ch

covering
natsSum : Logging io => LinearIO io =>
  {me : String} ->
  Nat -> -- accumulator
  Channel me them (Dual Sum) Nothing -@ L io ()
natsSum acc ch = do
  ch <- enter ch
  b # ch <- offer ch
  if b
    then do
      ch <- send ch acc
      close ch
    else do
      (n # ch) <- recv ch
      ch <- fold ch
      natsSum (acc + n) ch

covering
main : IO ()
main = do
  let %hint loggingIO : Logging IO; loggingIO = QUIET
  (sum, _) <- LIO.run $ fork Sum "A" "B" (sumNats [1..5]) (natsSum 0)
  putStrLn "Sum of [1..5] is \{show sum}"
