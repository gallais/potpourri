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

SendTypes : Session -> List Type
SendTypes (Send ty s) = ty :: SendTypes s
SendTypes (Recv ty s) = SendTypes s
SendTypes End = []

RecvTypes : Session -> List Type
RecvTypes (Send ty s) = RecvTypes s
RecvTypes (Recv ty s) = ty :: RecvTypes s
RecvTypes End = []

RecvDualTypes : (s : Session) -> RecvTypes (Dual s) === SendTypes s
RecvDualTypes (Send ty s) = cong (ty ::) (RecvDualTypes s)
RecvDualTypes (Recv ty s) = RecvDualTypes s
RecvDualTypes End = Refl

SendDualTypes : (s : Session) -> SendTypes (Dual s) === RecvTypes s
SendDualTypes (Send ty s) = SendDualTypes s
SendDualTypes (Recv ty s) = cong (ty ::) (SendDualTypes s)
SendDualTypes End = Refl

namespace Seen

  public export
  data Seen : Nat -> Nat -> (Session -> Session) -> Type where
    None : Seen 0 0 Prelude.id
    Recv : (ty : Type) -> Seen m n f -> Seen (S m) n (f . Recv ty)
    Send : (ty : Type) -> Seen m n f -> Seen m (S n) (f . Send ty)

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

atRecvIndex : Seen m _ f ->
          (s : Session) ->
          AtIndex ty (RecvTypes s) n ->
          AtIndex ty (RecvTypes (f s)) (m + n)
atRecvIndex None accS accAt = accAt
atRecvIndex (Recv ty s) accS accAt
  = rewrite plusSuccRightSucc (pred m) n in
    atRecvIndex s (Recv ty accS) (S accAt)
atRecvIndex (Send ty s) accS accAt
  = atRecvIndex s (Send ty accS) accAt

atSendIndex : Seen _ m f ->
          (s : Session) ->
          AtIndex ty (SendTypes s) n ->
          AtIndex ty (SendTypes (f s)) (m + n)
atSendIndex None accS accAt = accAt
atSendIndex (Recv ty s) accS accAt
  = atSendIndex s (Recv ty accS) accAt
atSendIndex (Send ty s) accS accAt
  = rewrite plusSuccRightSucc (pred m) n in
    atSendIndex s (Send ty accS) (S accAt)

export
record Channel (s : Session) where
  constructor MkChannel
  {sendStep     : Nat}
  {recvStep     : Nat}
  {0 seenPrefix : Session -> Session}
  0 seen        : Seen recvStep sendStep seenPrefix

  sendChan : Threads.Channel (Union Prelude.id (SendTypes (seenPrefix s)))
  recvChan : Threads.Channel (Union Prelude.id (RecvTypes (seenPrefix s)))

export
die1 : LinearIO io => String -> L1 io a
die1 err = do
  x <- die err
  pure1 x

export
recv : LinearIO io =>
       Channel (Recv ty s) -@
       L1 io (Res ty (const (Channel s)))
recv (MkChannel {recvStep} seen sendCh recvCh) = do
  --putStrLn "Receiving a value"
  x@(Element k prf val) <- channelGet recvCh
  let Just val = prj' (recvStep + 0) (atRecvIndex seen (Recv ty s) Z) x
    | Nothing => die1 "Oops: expected \{show recvStep} but got \{show k}"
  pure1 (val # MkChannel (Recv ty seen) sendCh recvCh)

export
send : LinearIO io =>
       (1 _ : Channel (Send ty s)) ->
       ty ->
       L1 io (Channel s)
send (MkChannel {sendStep} seen sendCh recvCh) x = do
  --putStrLn "Sending a value"
  let val = inj' (sendStep + 0) (atSendIndex seen (Send ty s) Z) x
  channelPut sendCh val
  pure1 (MkChannel (Send ty seen) sendCh recvCh)

export
end : LinearIO io => Channel End -@ L io ()
end (MkChannel _ _ _) = pure ()

export
fork : (s : Session) ->
       (Channel       s  -@ L IO a) -@
       (Channel (Dual s) -@ L IO b) -@
       L IO (a, b)
fork s kA kB = do
  sendChan <- makeChannel
  recvChan <- makeChannel
  aResChan <- makeChannel
  bResChan <- makeChannel
  let posCh : Channel s
    := MkChannel None sendChan recvChan
  let negCh : Channel (Dual s)
    := MkChannel None
         (rewrite SendDualTypes s in recvChan)
         (rewrite RecvDualTypes s in sendChan)
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
  putStrLn "0: Forking two threads"
  res <- fork (Recv Nat $ Recv Nat $ Send Nat End)
    (\ ch => do (m # ch) <- recv ch
                (n # ch) <- recv ch
                putStrLn "1: Received \{show m} and \{show n} and now summing them"
                ch <- send ch (m + n)
                end ch
                pure (m, n))
    (\ ch => do m <- cast <$> randomRIO {a = Int32} (0, 100)
                putStrLn "2: Randomly generated \{show m} and sending it to 1"
                ch <- send ch m
                n <- cast <$> randomRIO {a = Int32} (0, 100)
                putStrLn "2: Randomly generated \{show n} and sending it to 1"
                ch <- send ch n
                (s # ch) <- recv ch
                end ch
                pure s)
  let ((m, n), mplusn) = the ((Nat, Nat), Nat) res
  putStrLn {io = L IO} "0: Threads have finished and returned (\{show m}, \{show n}) and \{show mplusn}"
 --  putStrLn {io = L IO} "\{show m} + \{show n} = \{show mplusn}"
