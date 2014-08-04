module Main where

import Language
import Normalizer
import TypeChecking
import Data.Void

tmIdType :: Tm Void -> Tm Void
tmIdType a = piTm a $ piTm (TmVar Nothing) $ TmVar $ Just Nothing

nfIdType :: Nf Void -> Nf Void
nfIdType a = piNf a $ piNf (varNf Nothing) $ varNf $ Just Nothing

tmId :: Tm Void
tmId = lamTm $ lamTm $ TmVar Nothing

main :: IO ()
main =
  let tm = TmApp (TmApp tmId (tmIdType (tmIdType TmSet))
            (tmIdType TmSet))
            (piTm (tmIdType TmSet) $ TmVar Nothing) tmId in
  let nf = normClosed (nfIdType NfSet) tm in
  do
--     () <- print nf
--     () <- print (nfIdType NfSet)
    print $ check undefined NfSet (nfIdType NfSet)
--     print $ check undefined (nfIdType NfSet) nf
