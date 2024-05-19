module System.Concurrency.Session

import Control.Linear.LIO

import Data.Linear.Notation
import Data.List.AtIndex
import Data.Nat

import Data.OpenUnion
import System
import System.Concurrency as Threads
import System.Random

%default total

public export
data Session : Type where
  Send : (ty : Type) -> (s : Session) -> Session
  Recv : (ty : Type) -> (s : Session) -> Session
  End  : Session

public export
Dual : Session -> Session
Dual (Send ty s) = Recv ty (Dual s)
Dual (Recv ty s) = Send ty (Dual s)
Dual End = End

dualInvolutive : (s : Session) -> Dual (Dual s) === s
dualInvolutive (Send ty s) = cong (Send ty) (dualInvolutive s)
dualInvolutive (Recv ty s) = cong (Recv ty) (dualInvolutive s)
dualInvolutive End = Refl

(++) : Session -> Session -> Session
Send ty s ++ t = Send ty (s ++ t)
Recv ty s ++ t = Recv ty (s ++ t)
End ++ t = t

namespace Seen

  public export
  data Seen : Nat -> (Session -> Session) -> Type where
    None : Seen 0 Prelude.id
    Recv : (ty : Type) -> Seen n f -> Seen (S n) (f . Recv ty)
    Send : (ty : Type) -> Seen n f -> Seen (S n) (f . Send ty)

{-
Types : Session -> List Type
Types (Send ty s) = ty :: Types s
Types (Recv ty s) = ty :: Types s
Types End = []

typesDual : (s : Session) -> Types (Dual s) === Types s
typesDual (Send ty s) = cong (ty ::) (typesDual s)
typesDual (Recv ty s) = cong (ty ::) (typesDual s)
typesDual End = Refl

atIndex : Seen m f ->
          (s : Session) ->
          AtIndex ty (Types s) n ->
          AtIndex ty (Types (f s)) (m + n)
atIndex None accS accAt = accAt
atIndex (Recv ty s) accS accAt
  = rewrite plusSuccRightSucc (pred m) n in
    atIndex s (Recv ty accS) (S accAt)
atIndex (Send ty s) accS accAt
  = rewrite plusSuccRightSucc (pred m) n in
    atIndex s (Send ty accS) (S accAt)
-}


SendTypes : Session -> List Type
SendTypes (Send ty s) = ty :: SendTypes s
SendTypes (Recv ty s) = SendTypes s
SendTypes End = []

RecvTypes = SendTypes . Dual

export
record Channel (s : Session) where
  constructor MkChannel
  {sendStep     : Nat}
  {0 sendPrefix : Session -> Session}
  0 sendSeen    : Seen seenStep seenPrefix
  sendChan : Threads.Channel (Union Prelude.id (SendTypes (sendPrefix s)))

  {recvStep     : Nat}
  {0 recvPrefix : Session -> Session}
  0 recvSeen    : Seen recvStep recvPrefix
  recvChan : Threads.Channel (Union Prelude.id (RecvTypes (recvPrefix s)))

{-
export
die1 : LinearIO io => String -> L1 io a
die1 err = do
  x <- die err
  pure1 x

export
recv : LinearIO io =>
       Channel (Recv ty s) -@
       L1 io (Res ty (const (Channel s)))
recv (MkChannel {step} seen rawCh) = do
  putStrLn "Receiving a value"
  x@(Element k prf val) <- channelGet rawCh
  let Just val = prj' (step + 0) (atIndex seen ? Z) x
    | Nothing => die1 "Oops: expected \{show step} but got \{show k}"
  pure1 (val # MkChannel (Recv ty seen) rawCh)

export
send : LinearIO io =>
       (1 _ : Channel (Send ty s)) ->
       ty ->
       L1 io (Channel s)
send (MkChannel {step} seen rawCh) x = do
  putStrLn "Sending a value"
  let val = inj' (step + 0) (atIndex seen ? Z) x
  channelPut rawCh val
  pure1 (MkChannel (Send ty seen) rawCh)

export
end : LinearIO io => Channel End -@ L io ()
end (MkChannel _ _) = pure ()

export
fork : (s : Session) ->
       (Channel       s  -@ L IO a) -@
       (Channel (Dual s) -@ L IO b) -@
       L IO (a, b)
fork s kA kB = do
  commChan <- makeChannel
  aResChan <- makeChannel
  bResChan <- makeChannel
  let posCh : Channel s
    := MkChannel None commChan
  let negCh : Channel (Dual s)
    := MkChannel None (rewrite typesDual s in commChan)
  _ <- liftIO1 $ IO.fork $ LIO.run $
         do x <- kA posCh
            channelPut aResChan x
  _ <- liftIO1 $ IO.fork $ LIO.run $
         do y <- kB negCh
            channelPut bResChan y
  x <- channelGet aResChan
  y <- channelGet bResChan
  pure (x, y)

main : IO ()
main = LIO.run $ do
  res <- fork (Recv Nat $ Recv Nat $ Send Nat End)
    (\ ch => do (m # ch) <- recv ch
                (n # ch) <- recv ch
                ch <- send ch (m + n)
                end ch
                pure (m, n))
    (\ ch => do m <- cast <$> randomRIO {a = Int32} (0, 100)
                n <- cast <$> randomRIO {a = Int32} (0, 100)
                ch <- send ch m
                ch <- send ch n
                (s # ch) <- recv ch
                end ch
                pure s)
  let ((m, n), mplusn) = the ((Nat, Nat), Nat) res
  printLn {io = L IO} "\{show m} + \{show n} = \{show mplusn}"
-}
