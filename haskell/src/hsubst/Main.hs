module Main where

import Language
import Normalizer
import TypeChecking
import Data.Void

succTm :: Tm a
succTm = lamTm $ TmSuc $ TmVar Nothing

plusTm :: Tm a
plusTm =
  lamTm {- m -} $
  lamTm {- n -} $
  TmRec (lamTm TmNat) (lamTm succTm) (TmVar Nothing)
        (TmVar $ Just Nothing)

plus :: Tm a -> Tm a -> Tm a
plus m n =
  TmApp plusTm (arrTm TmNat $ arrTm TmNat TmNat) $
    Sp [ ElimApp m, ElimApp n ]

double :: Tm a -> Tm a
double m = plus m m

oneTm   = TmSuc TmZro
twoTm   = double oneTm
fourTm  = double twoTm
eightTm = double fourTm
tenTm   = plus eightTm twoTm

arityN :: Tm a
arityN =
  lamTm {- A -} $
  lamTm {- n -} $
  TmRec
    (lamTm TmSet)
    (lamTm $ lamTm $ arrTm (TmVar Nothing)
                           (TmVar Nothing))
    (TmVar $ Just Nothing)
    (TmVar Nothing)

arityNty :: Tm a
arityNty = piTm TmSet $ arrTm TmNat $ TmSet

arityNat2 =
  TmApp arityN arityNty $ Sp [ ElimApp TmNat, ElimApp twoTm ]

tmIdType :: Tm Void -> Tm Void
tmIdType a = piTm a $ piTm (TmVar Nothing) $ TmVar $ Just Nothing

nfIdType :: Nf Void -> Nf Void
nfIdType a = piNf a $ piNf (varNf Nothing) $ varNf $ Just Nothing

tmId :: Tm Void
tmId = lamTm $ lamTm $ TmVar Nothing

main :: IO ()
main =
  let args  = Sp $ [ ElimApp (tmIdType TmSet), ElimApp tmId ]
      tm    = TmApp tmId (tmIdType TmSet) args
      nf    = normClosed (nfIdType NfSet) tm
      sumty = normClosed NfSet (arrTm TmNat $ arrTm TmNat TmNat)
      sum   = normClosed NfNat tenTm
      arN4  = normClosed NfSet arityNat2
  in do
    () <- print nf
    () <- print sumty
    () <- print sum
    () <- print arN4
    () <- print (nfIdType NfSet)
    print $ check undefined NfSet (nfIdType NfSet)
    print $ check undefined sumty $ normClosed sumty plusTm
    print $ check undefined (nfIdType NfSet) nf
