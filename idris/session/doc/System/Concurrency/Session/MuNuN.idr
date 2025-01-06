module System.Concurrency.Session.MuNuN

import Control.Linear.LIO

import Data.DPair
import Data.List.HasLength
import Data.List.AtIndex
import Data.Nat
import Data.SnocList

import Data.OpenUnion
import System
import System.File
import System.Concurrency as Threads
import System.Concurrency.Linear

%default total


interface Logging io where
  logging : LinearIO io => String -> L io ()

[LOG] Logging io where
  logging = putStrLn
[QUIET] Logging io where
  logging str = pure ()

------------------------------------------------------------------------
-- Session types

namespace Kinds

  public export
  Name : Type
  Name = String

  public export
  data Kind : Type where
    Mu, Nu : Name -> Kind

  public export
  Dual : Kind -> Kind
  Dual (Mu nm) = (Nu nm)
  Dual (Nu nm) = (Mu nm)

  export
  dualInvolutive : (kd : Kind) -> Dual (Dual kd) === kd
  dualInvolutive (Mu _) = Refl
  dualInvolutive (Nu _) = Refl

  public export
  Kinds : Type
  Kinds = List Kind -- TODO: snoclists

namespace Focus

  public export
  data Focus : (nm : Kind) -> (nms : Kinds) -> Type where
    MkFocus :
      (thePrefix : SnocList Kind) ->
      (kd : Kind) ->
      (theSuffix : Kinds) ->
      {auto theProof : nms === (thePrefix <>> kd :: theSuffix)} ->
      Focus kd nms

  export
  Uninhabited (Focus nm []) where
    uninhabited = go Refl where
      go : [] === xs -> Focus x xs -> Void
      go eq (MkFocus [<] _ suff @{Refl}) = case eq of {}
      go eq foc@(MkFocus (pref :< x) nm suff @{Refl})
        = go eq (assert_smaller foc (MkFocus pref x (nm :: suff)))

  public export
  theSuffix : Focus nm nms -> Kinds
  theSuffix (MkFocus _ _ suff) = suff

  public export
  Dual : Focus nm nms -> Focus (Dual nm) (map Dual nms)
  Dual (MkFocus thePrefix kd theSuffix @{eq})
    = MkFocus (map Dual thePrefix) (Dual kd) (map Dual theSuffix)
      @{believe_me eq} -- TODO: fix

namespace Session

  public export
  data Norm = Head | Expr

  ||| A session type describes the interactions one thread may have with
  ||| another over a shared bidirectional channel: it may send or receive
  ||| values of arbitrary types, or be done communicating.
  public export
  data Session : Kinds -> Norm -> Type where
    -- Recursive parts
    Fix : (kd : Kind) -> (s : Session (kd :: nms) Head) -> Session nms Head
    Rec : {kd : Kind} -> Focus kd nms -> Session nms Expr
    -- Usual operations
    Send : (ty : Type) -> (s : Session nms n) -> Session nms Head
    Recv : (ty : Type) -> (s : Session nms n) -> Session nms Head
    -- End a session
    End : Session nms Head
    -- Choice
    Offer : (s : Session nms m1) -> (t : Session nms m2) -> Session nms Head
    Select : (s : Session nms m1) -> (t : Session nms m2) -> Session nms Head

  ||| Dual describes how the other party to the communication sees the
  ||| interactions: our sends become their receives and vice-versa.
  public export
  Dual : Session nms m -> Session (map Dual nms) m
  Dual (Fix kd s) = Fix (Dual kd) (Dual s)
  Dual (Rec pos) = Rec (Dual pos)
  Dual (Send ty s) = Recv ty (Dual s)
  Dual (Recv ty s) = Send ty (Dual s)
  Dual End = End
  Dual (Offer s t) = Select (Dual s) (Dual t)
  Dual (Select s t) = Offer (Dual s) (Dual t)

{-
  ||| Duality is involutive: the dual of my dual is me
  export
  dualInvolutive : (s : Session nms m) -> Dual (Dual s) === s
  dualInvolutive (Fix nm kd s) = cong2 (Fix nm) (dualInvolutive kd) (dualInvolutive s)
  dualInvolutive (Rec pos) = Refl
  dualInvolutive (Send ty s) = cong (Send ty) (dualInvolutive s)
  dualInvolutive (Recv ty s) = cong (Recv ty) (dualInvolutive s)
  dualInvolutive End = Refl
  dualInvolutive (Offer s t) = cong2 Offer (dualInvolutive s) (dualInvolutive t)
  dualInvolutive (Select s t) = cong2 Select (dualInvolutive s) (dualInvolutive t)
-}

||| We can collect the list of types that will be sent over the
||| course of a session by walking down its description
||| This definition is purely internal and will not show up in
||| the library's interface.
SendTypes : Session nms m -> List Type
SendTypes (Fix kd s) = SendTypes s
SendTypes (Rec pos) = []
SendTypes (Send ty s) = ty :: SendTypes s
SendTypes (Recv ty s) = SendTypes s
SendTypes End = []
SendTypes (Offer s1 s2) = SendTypes s1 ++ SendTypes s2
SendTypes (Select s1 s2) = SendTypes s1 ++ SendTypes s2

||| We can collect the list of types that will be received over
||| the course of a session by walking down its description
||| This definition is purely internal and will not show up in
||| the library's interface.
RecvTypes : Session nms m -> List Type
RecvTypes (Fix kd s) = RecvTypes s
RecvTypes (Rec pos) = []
RecvTypes (Send ty s) = RecvTypes s
RecvTypes (Recv ty s) = ty :: RecvTypes s
RecvTypes End = []
RecvTypes (Offer s1 s2) = RecvTypes s1 ++ RecvTypes s2
RecvTypes (Select s1 s2) = RecvTypes s1 ++ RecvTypes s2

||| The types received by my dual are exactly the ones I am sending
||| This definition is purely internal and will not show up in
||| the library's interface.
RecvDualTypes : (s : Session nms m) -> RecvTypes (Dual s) === SendTypes s
RecvDualTypes (Fix kd s) = RecvDualTypes s
RecvDualTypes (Rec pos) = Refl
RecvDualTypes (Send ty s) = cong (ty ::) (RecvDualTypes s)
RecvDualTypes (Recv ty s) = RecvDualTypes s
RecvDualTypes End = Refl
RecvDualTypes (Offer s1 s2) = cong2 (++) (RecvDualTypes s1) (RecvDualTypes s2)
RecvDualTypes (Select s1 s2) = cong2 (++) (RecvDualTypes s1) (RecvDualTypes s2)

||| The types sent by my dual are exactly the ones I receive
||| This definition is purely internal and will not show up in
||| the library's interface.
SendDualTypes : (s : Session nms m) -> SendTypes (Dual s) === RecvTypes s
SendDualTypes (Fix kd s) = SendDualTypes s
SendDualTypes (Rec pos)= Refl
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
  data Loop : Session nms Head -> Nat -> Nat -> Session nms k2 -> Type where
    Lin  : Loop o 0 0 o
    (:<) : Loop o p q s' -> Headed m n s' s'' -> Loop o (p + m) (q + n) s''

  export
  (:<!) : Loop o p q s' -> Headed m n s' s'' -> Loop o (m + p) (n + q) s''
  pref :<! hd
    = rewrite plusCommutative m p in
      rewrite plusCommutative n q in
      pref :< hd

-- TODO: snoc
namespace Env

  public export
  data Env : Kinds -> Type where
    Nil  : Env []
    (::) : Session (nm :: nms) Head -> Env nms -> Env (nm :: nms)

  public export
  head : Env (e :: nms) -> Session (e :: nms) Head
  head (s :: _) = s

  public export
  tail : Env (e :: nms) -> Env nms
  tail (_ :: env) = env

  public export
  lookup : (f : Focus nm nms) -> Env nms -> Env (nm :: theSuffix f)
  lookup (MkFocus [<] nm suff @{Refl}) env = env
  lookup foc@(MkFocus (sx :< x) nm suff @{prf}) env
    = tail (lookup (assert_smaller foc (MkFocus sx x (nm :: suff) @{prf})) env)

  public export
  etaEnvCons : (env : Env (nm :: nms)) -> env === head env :: tail env
  etaEnvCons (_ :: _) = Refl

public export
data Context : Nat -> Nat -> Session m1 k1 -> Session m2 k2 -> Env m2 -> Type where
  InPrefix : {p, q : Nat} -> (0 pref : Prefix p q s s') ->
             Context p q s s' []
  Pumping  : {m, n, p, q : Nat} -> (ctx : Context p q s (Fix kd o) env) ->
             (0 loop : Loop o m n s') ->
             Context (p + m) (q + n) s s' (o :: env)

Sumer : Session [] Head
Sumer
  = Fix (Nu "serve")
  $ Offer End
  $ Send String
  $ Fix (Nu "getNs")
  $ Offer
      (Send Nat $ Rec (MkFocus [<(Nu "getNs")] (Nu "serve") []))
      (Recv Nat $ Rec (MkFocus [<] (Nu "getNs") [(Nu "serve")]))

sumerCtx
  : Context 1 2 Sumer (Rec (MkFocus [<] (Nu "getNs") [(Nu "serve")]))
       [ Offer
          (Send Nat $ Rec (MkFocus [<(Nu "getNs")] (Nu "serve") []))
          (Recv Nat $ Rec (MkFocus [<] (Nu "getNs") [(Nu "serve")]))
       , Offer End $ Send String $ Fix (Nu "getNs") $ Offer
          (Send Nat $ Rec (MkFocus [<(Nu "getNs")] (Nu "serve") []))
          (Recv Nat $ Rec (MkFocus [<] (Nu "getNs") [(Nu "serve")]))
       ]
sumerCtx
  = Pumping (Pumping (InPrefix [<]) [<OfferR, Send String])
  $ [< OfferR, Recv Nat]

export
record Channel (me, them : String) (s : Session nms k) (e : Env nms) where
  constructor MkChannel
  {sendStep    : Nat}
  {recvStep    : Nat}
  {0 ogNorm    : Norm}
  {0 ogKinds   : Kinds}
  {0 ogSession : Session ogKinds ogNorm}
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
    recvContext pref (recvLoop loop idx)

Recv :
  (0 ty : Type) ->
  Context m n s (Recv ty s') e ->
  Context (S m) n s s' e
Recv ty (InPrefix pref)
  = InPrefix (pref :<! Recv ty)
Recv ty (Pumping {p, q, m, n} ctx loop)
  = rewrite plusSuccRightSucc p m in
    Pumping ctx (loop :<! Recv ty)

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
sendContext (Pumping {q, n} ctx loop) idx
  = rewrite sym $ plusAssociative q n i in
    sendContext ctx (sendLoop loop idx)

Send :
  (0 ty : Type) ->
  Context m n s (Send ty s') e ->
  Context m (S n) s s' e
Send ty (InPrefix pref)
  = InPrefix (pref :<! Send ty)
Send ty (Pumping {p, q, m, n} ctx loop)
  = rewrite plusSuccRightSucc q n in
    Pumping ctx (loop :<! Send ty)

Enter :
  {m, n : Nat} ->
  Context m n s (Fix kd o) e ->
  Context m n s o (o :: e)
Enter ctx
  = rewrite plusCommutative 0 m in
    rewrite plusCommutative 0 n in
    Pumping ctx [<]


namespace Context

  export
  head :
    Context m n s _ env ->
    (m : Nat ** n : Nat ** Context m n s (head env) env)
  head (Pumping {p, q} ctx loop)
    = MkDPair p
    $ MkDPair q
    $ rewrite plusCommutative 0 p in
      rewrite plusCommutative 0 q in
      Pumping ctx [<]

  export
  tail :
    Context m n s s2 env ->
    (m : Nat ** n : Nat ** Context m n s (head (tail env)) (tail env))
  tail (Pumping ctx loop) = head ctx

UnfoldAux :
  (pos : Focus nm nms) ->
  Context m n s s2 env ->
  (m : Nat ** n : Nat ** Context m n s (head (lookup pos env)) (lookup pos env))
UnfoldAux pos (InPrefix pref) = absurd pos
UnfoldAux (MkFocus [<] nm theSuffix @{Refl}) ctx@(Pumping _ _)
  = head ctx
UnfoldAux foc@(MkFocus (sx :< x) nm suff @{prf}) ctx@(Pumping _ _)
  = let (_ ** _ ** ctx) = UnfoldAux (assert_smaller foc (MkFocus sx x (nm :: suff) @{prf})) ctx in
    tail ctx

Unfold :
  (pos : Focus nm nms) ->
  Context m n s (Rec pos) env ->
  (m : Nat ** n : Nat ** Context m n s (head (lookup pos env)) (lookup pos env))
Unfold pos = UnfoldAux {s2 = Rec pos} pos

FoldAux :
  Context m n s o (o :: env) ->
  (m : Nat ** n : Nat ** Context m n s (Fix kd o) env)
FoldAux (Pumping ctx loop) = (_ ** _ ** ctx)

Fold :
  (pos : Focus kd nms) ->
  Context m n s (Rec pos) env ->
  (m : Nat ** n : Nat ** Context m n s (Fix kd (head (lookup pos env))) (tail (lookup pos env)))
Fold pos ctx = case Unfold pos ctx of
  (p ** q ** ctx) => FoldAux (rewrite sym (etaEnvCons (lookup pos env)) in ctx)

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
OfferL (Pumping ctx loop) = Pumping ctx (loop :<! OfferL)

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
send : LinearIO io =>
  Logging io => {me : String} -> Show ty =>
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
  Channel me them (Fix nm s) e -@
  L1 io (Channel me them s (s :: e))
enter (MkChannel ctxt sendCh recvCh) = do
  pure1 (MkChannel (Enter ctxt) sendCh recvCh)

export
unfold : LinearIO io =>
  {pos : _} ->
  Channel me them (Rec pos) e -@
  L1 io (Channel me them (head (lookup pos e)) (lookup pos e))
unfold (MkChannel ctxt sendCh recvCh) = do
  let (p ** q ** ctxt) = Unfold pos ctxt
  pure1 (MkChannel ctxt sendCh recvCh)

namespace Guard

  -- Do NOT export the constructor
  export
  data Guarded : Type -> Type where
    MkGuarded : (1 _ : a) -> Guarded a

  runGuarded : (1 _ : Guarded a) -> a
  runGuarded (MkGuarded v) = v

  public export
  Guard : Kind -> Type -> Type
  Guard (Mu _) a = a
  Guard (Nu _) a = Guarded a

  public export %tcinline
  callGuarded1 : ((1 _ : a) -> b) -> (1 _ : Guarded a) -> b
  callGuarded1 f x = assert_total (f (runGuarded x))

  export
  fold : LinearIO io =>
    {pos : Focus kd nms} ->
    Channel me them (Rec pos) e -@
    L1 io (Guard kd (Channel me them (Fix kd (head (lookup pos e))) (tail (lookup pos e))))
  fold (MkChannel ctxt sendCh recvCh) = do
    let (p ** q ** ctxt) = Fold pos ctxt
    let 1 ch : Channel me them (Fix kd (head (lookup pos e))) (tail (lookup pos e))
             := MkChannel ctxt sendCh recvCh
    pure1 (assert_linear believe_me ch)

export
close : LinearIO io =>
  Channel me them End e -@
  L io ()
close (MkChannel{}) = pure ()

||| Given a session, create a bidirectional communication channel and
||| return its two endpoints
export
makeChannel :
  LinearIO io =>
  (0 s : Session [] m) ->
  L1 io (LPair (Channel me them s []) (Channel them me (Dual s) []))
makeChannel s = do
  sendChan <- Threads.makeChannel
  recvChan <- Threads.makeChannel
  let 1 posCh : Channel me them s []
    := MkChannel (InPrefix [<]) sendChan recvChan
  let 1 negCh : Channel them me (Dual s) []
    := MkChannel (InPrefix [<])
         (rewrite SendDualTypes s in recvChan)
         (rewrite RecvDualTypes s in sendChan)
  pure1 (posCh # negCh)

||| Given a session and two functions communicating according to that
||| sesion, we can run the two programs concurrently and collect their
||| final results.
||| The `src` and `tgt` names are purely for logging purposes.
export
fork : (0 s : Session [] m) ->
       (me, them : String) ->
       (Channel me them s        [] -@ L IO a) -@
       (Channel them me (Dual s) [] -@ L IO b) -@
       L IO (a, b)
fork s me them kA kB = do
  (posCh # negCh) <- MuNuN.makeChannel s
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


sumNatss : LinearIO io =>
  Logging io => {me : String} ->
  List (List Nat) -> -- list of arguments
  SnocList Nat -> -- accumulator of results
  Channel me them (Dual Sumer) [] -@ L io (List Nat)

sumNats : LinearIO io =>
  Logging io => {me : String} ->
  List Nat -> -- list of arguments
  List (List Nat) -> -- list of list arguments
  SnocList Nat -> -- accumulator of results
  Channel me them (Dual $ Offer
        (Send Nat $ Rec (MkFocus [<Nu "getNs"] (Nu "serve") []))
        (Recv Nat $ Rec (MkFocus [<] (Nu "getNs") [(Nu "serve")])))
    [ Dual $ Offer
        (Send Nat $ Rec (MkFocus [<Nu "getNs"] (Nu "serve") []))
        (Recv Nat $ Rec (MkFocus [<] (Nu "getNs") [(Nu "serve")]))
    , Dual $ Offer End $ Send String $ Fix (Nu "getNs") $ Offer
        (Send Nat $ Rec (MkFocus [<Nu "getNs"] (Nu "serve") []))
        (Recv Nat $ Rec (MkFocus [<] (Nu "getNs") [(Nu "serve")]))
    ]
 -@ L io (List Nat)

sumNatss [] acc ch = do
  ch <- enter ch
  ch <- select ch True
  close ch
  pure (acc <>> [])
sumNatss (ns :: nss) acc ch = do
  ch <- enter ch
  ch <- select ch False
  (msg # ch) <- recv ch
  putStrLn msg
  ch <- enter ch
  sumNats ns nss acc ch

sumNats [] nss acc ch = do
  ch <- select ch True
  (n # ch) <- recv ch
  ch <- fold ch
  sumNatss nss (acc :< n) ch
sumNats (n :: ns) nss acc ch = do
  ch <- select ch False
  ch <- send ch n
  ch <- unfold ch
  sumNats ns nss acc ch

natssSum : LinearIO io =>
  Logging io => {me : String} ->
  Nat -> -- ID
  Channel me them Sumer [] -@ L io ()

natsSum : LinearIO io =>
  Logging io => {me : String} ->
  Nat -> -- accumulator
  Channel me them (Fix (Nu ("getNs")) $ Offer
        (Send Nat $ Rec (MkFocus [<(Nu "getNs")] (Nu "serve") []))
        (Recv Nat $ Rec (MkFocus [<] (Nu "getNs") [(Nu "serve")])))
    [ Offer End $ Send String $ Fix (Nu "getNs") $ Offer
        (Send Nat $ Rec (MkFocus [<(Nu "getNs")] (Nu "serve") []))
        (Recv Nat $ Rec (MkFocus [<] (Nu "getNs") [(Nu "serve")]))
    ] -@
    L1 io (Guarded (Channel me them Sumer []))

natssSum id ch = do
  ch <- enter ch
  b # ch <- offer ch
  if b
    then do
      close ch
    else do
      ch <- send ch "Welcome, you are our client n°\{show id}"
      ch <- natsSum 0 ch
      callGuarded1 (natssSum (S id)) ch
natsSum acc ch = do
  ch <- enter ch
  b # ch <- offer ch
  if b
    then do
      ch <- send ch acc
      ch <- fold ch
      pure1 ch
    else do
      (n # ch) <- recv ch
      ch <- fold ch
      callGuarded1 (natsSum (acc + n)) ch


main : IO ()
main = do
  let %hint loggingIO : Logging IO; loggingIO = QUIET
  (_, sums) <- LIO.run $ fork Sumer "A" "B" (natssSum 0) (sumNatss [[1..5], [5..10]] [<])
  putStrLn "Results are \{show sums}"
