module Main where

import Language
import Normalizer
import TypeChecking
import Data.Void

type TmType = Ty Tm Void
type TmTerm = Tm Void

type NfType = Ty Nf Void
type NfTerm = Nf Void

tmIdType :: TmType -> TmType
tmIdType a = piTm a $ piTm (TyElt $ TmVar Nothing) $
             TyElt $ TmVar $ Just Nothing

nfIdType :: NfType -> NfType
nfIdType a = piNf a $ piNf (TyElt $ varNf Nothing) $
             TyElt $ varNf $ Just Nothing

tmId :: TmTerm
tmId = lamTm $ lamTm $ TmVar Nothing

main :: IO ()
main =
  let args  = Sp $ [ ElimApp (TmTyp $ tmIdType TySet), ElimApp tmId ]
      tm    = TmApp tmId (tmIdType TySet) args
      nf    = normClosed (nfIdType TySet) tm
  in do
    () <- print tm
    () <- print args
    print nf
