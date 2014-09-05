module Main where

import Language
import HSubst
import Normalizer
import Data.Void
import Debug.Trace

type TmType = Ty Tm Void Void
type TmTerm = Tm Void Void

type NfType = Ty Ne Void Void
type NfTerm = Nf Void Void

-- identity
tmIdType :: TmType -> TmType
tmIdType a = tyAbs a $ tyAbs (TyElt $ TmVar Nothing) $
             TyElt $ TmVar $ Just Nothing

nfIdType :: NfType -> NfType
nfIdType a = tyAbs a $ tyAbs (TyElt $ varNe Nothing) $
             TyElt $ varNe $ Just Nothing

tmId :: TmTerm
tmId = lamTm $ lamTm $ TmVar Nothing

-- natural numbers
natDesc :: ScopeDa (Ty Tm) Void Void
natDesc =
  ScopeDa $
    TySig TyTwo $ ScopeTm $ TyElt $
      TmApp (TmVar Nothing) TyTwo $
      Sp [ ElimTwo (tyArr TyTwo TyDat)
                   (TmTyp TyOne)
                   (TmTyp $ TyVar Nothing) ]

nat :: NfType
nat = normTy nat'

zro :: NfTerm
zro = NfInM $ NfSig NfTru NfOne

suc :: NfTerm -> NfTerm
suc n = NfInM $ NfSig NfFls n

main :: IO ()
main =
  let args :: Sp Tm Tm Void Void
      args  = Sp $ [ ElimApp (TmTyp $ tmIdType TySet), ElimApp tmId ]
      tm    = TmApp tmId (tmIdType TySet) args
      nf    = normClosed (nfIdType TySet) tm
  in do
    () <- putStrLn $ "Nat    : " ++ show nat
    () <- putStrLn $ "0      : " ++ show zro
    () <- putStrLn $ "1      : " ++ show one
    () <- putStrLn $ "id $ id: " ++ show tm
    () <- putStrLn $ "args   : " ++ show args
    () <- putStrLn $ "id     : " ++ show nf
    () <- putStrLn $ "2      : " ++ show (suc one)
    return ()
