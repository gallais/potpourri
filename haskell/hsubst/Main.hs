module Main where

import Language
import HSubst
import Normalizer
import Data.Void
import Debug.Trace

type TmType = Ty Tm Void Void
type TmTerm = Tm Void Void

type NfType = Ty Nf Void Void
type NfTerm = Nf Void Void

-- identity
tmIdType :: TmType -> TmType
tmIdType a = tyAbs a $ tyAbs (TyElt $ TmVar Nothing) $
             TyElt $ TmVar $ Just Nothing

nfIdType :: NfType -> NfType
nfIdType a = tyAbs a $ tyAbs (TyElt $ varNf Nothing) $
             TyElt $ varNf $ Just Nothing

tmId :: TmTerm
tmId = lamTm $ lamTm $ TmVar Nothing

-- natural numbers
natDesc :: ScopeDa (Ty Nf) Void Void
natDesc =
  ScopeDa $
    TySig TyTwo $ ScopeTm $ TyElt $ NfNeu $
    Ne Nothing $ Sp [ ElimTwo (tyArr TyTwo TyDat)
                              (NfTyp TyOne)
                              (NfRec Nothing) ]

nat :: NfType
nat = TyRec natDesc

zro :: NfTerm
zro = NfInM $ NfSig NfTru NfOne

suc :: NfTerm -> NfTerm
suc n = NfInM $ NfSig NfFls n

main :: IO ()
main =
  let args  = Sp $ [ ElimApp (TmTyp $ tmIdType TySet), ElimApp tmId ]
      tm    = TmApp tmId (tmIdType TySet) args
      nf    = normClosed (nfIdType TySet) tm
  in do
    () <- putStrLn $ "Nat    : " ++ show nat
    () <- putStrLn $ "0      : " ++ show zro
    () <- putStrLn $ "1      : " ++ show (suc zro)
    () <- putStrLn $ "id $ id: " ++ show tm
    () <- print args
    putStrLn       $ "id     : " ++ show nf
