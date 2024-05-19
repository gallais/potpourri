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

interface LogLevel where
  constructor MkLogLevel
  logLevel : Nat

logging : LinearIO io => LogLevel => Nat -> String -> L io ()
logging lvl str = when (logLevel >= lvl) $ putStrLn str

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
record Channel (src, tgt : nm) (s : Session) where
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
recv : {src, tgt : String} -> Show ty => LogLevel =>
  LinearIO io =>
  Channel src tgt (Recv ty s) -@
  L1 io (Res ty (const (Channel src tgt s)))
recv (MkChannel {recvStep} seen sendCh recvCh) = do
  x@(Element k prf val) <- channelGet recvCh
  let Just val = prj' (recvStep + 0) (atRecvIndex seen (Recv ty s) Z) x
    | Nothing => die1 "Oops: expected \{show recvStep} but got \{show k}"
  logging 3 "\{src}: received \{show val} from \{tgt}"
  pure1 (val # MkChannel (Recv ty seen) sendCh recvCh)

export
send : {src, tgt : String} -> Show ty => LogLevel =>
  LinearIO io =>
  (1 _ : Channel src tgt (Send ty s)) ->
  ty ->
  L1 io (Channel src tgt s)
send (MkChannel {sendStep} seen sendCh recvCh) x = do
  let val = inj' (sendStep + 0) (atSendIndex seen (Send ty s) Z) x
  channelPut sendCh val
  logging 3 "\{src}: sent \{show x} to \{tgt}"
  pure1 (MkChannel (Send ty seen) sendCh recvCh)

export
end : {src, tgt : String} -> LogLevel =>
  LinearIO io => Channel src tgt End -@ L io ()
end (MkChannel _ _ _) = do
  logging 3 "\{src}: closing channel to \{tgt}"
  pure ()

export
fork : (src, tgt : nm) ->
       (s : Session) ->
       ((me : nm) -> {them : nm} -> Channel me them       s  -@ L IO a) -@
       ((me : nm) -> {them : nm} -> Channel me them (Dual s) -@ L IO b) -@
       L IO (a, b)
fork src tgt s kA kB = do
  sendChan <- makeChannel
  recvChan <- makeChannel
  aResChan <- makeChannel
  bResChan <- makeChannel
  let posCh : Channel src tgt s
    := MkChannel None sendChan recvChan
  let negCh : Channel tgt src (Dual s)
    := MkChannel None
         (rewrite SendDualTypes s in recvChan)
         (rewrite RecvDualTypes s in sendChan)
  _ <- liftIO1 $ IO.fork $ LIO.run $
         do x <- kA src {them = tgt} posCh
            channelPut aResChan x
  _ <- liftIO1 $ IO.fork $ LIO.run $
         do y <- kB tgt {them = src} negCh
            channelPut bResChan y
  x <- channelGet aResChan
  y <- channelGet bResChan
  pure (x, y)

main : IO ()
main = LIO.run $ do
  let nm1 : String := "natrando"
  let nm2 : String := "computer"
  let lvl : LogLevel := MkLogLevel 3
  logging 2 "main: Forking two threads \{nm1} and \{nm2}"
  res <- fork nm1 nm2 (Send Nat $ Send Nat $ Recv Nat End)
    (\ me, ch =>
             do m <- cast <$> randomRIO {a = Int32} (0, 100)
                logging 1 "\{me}: randomly generated \{show m}"
                ch <- send ch m
                n <- cast <$> randomRIO {a = Int32} (0, 100)
                logging 1 "\{me}: randomly generated \{show n}"
                ch <- send ch n
                (s # ch) <- recv ch
                end ch
                pure (m, n))
    (\ me, ch =>
             do (m # ch) <- recv ch
                (n # ch) <- recv ch
                logging 1 "\{me}: summing \{show m} and \{show n}"
                let s = m + n
                ch <- send ch s
                end ch
                pure s)
  let mn = fst res
  let mplusn = snd res
  logging {io = IO} 2 "main: Threads have finished and returned \{show mn} and \{show mplusn}"
