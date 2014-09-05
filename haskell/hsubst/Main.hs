module Main where

import Language
import Context
import HSubst
import Normalizer
import Data.Void
import Data.Bifunctor

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
natDesc :: ScopeDa (Ty Tm) a b
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

nat' :: Ty Tm a b
nat' = TyRec natDesc

zro' :: TmTerm
zro' = TmInM $ TmSig TmTru TmOne

suc' :: Tm a b -> Tm a b
suc' n = TmInM $ TmSig TmFls n

one :: NfTerm
one = suc zro

one' :: TmTerm
one' = suc' zro'

plus' :: TmTerm -> TmTerm -> TmTerm
plus' m n =
  TmApp m nat' $ Sp [ ElimRec natDesc (tyArr nat' nat') $
     lamTm {- m' -} $
     lamTm {- ih -} $
     TmApp {- m' -} (TmVar $ Just Nothing) inTyNat $ Sp
      [ ElimPr1
      , ElimTwo (tyArr TyTwo nat')
           (second (Just . Just) n)
           (suc' (TmVar Nothing)) ] ]
  where
    inTyNat =
      TySig TyTwo $ ScopeTm $ TyElt $
        TmApp (TmVar Nothing) TyTwo $
        Sp [ ElimTwo (tyArr TyTwo TySet)
                     (TmTyp TyOne)
                     (TmTyp nat') ]

two :: NfTerm
two = norm nat $ plus' one' one'

four :: NfTerm
four = norm nat $ plus' (plus' one' one') (plus' one' one')

main :: IO ()
main =
  let args :: Sp Tm Tm Void Void
      args  = Sp $ [ ElimApp (TmTyp $ tmIdType TySet), ElimApp tmId ]
      tm    = TmApp tmId (tmIdType TySet) args
      nf    = normClosed (nfIdType TySet) tm
  in do
    () <- putStrLn $ "Nat        : " ++ show nat
    () <- putStrLn $ "0          : " ++ show zro
    () <- putStrLn $ "1          : " ++ show one
    () <- putStrLn $ "id $ id    : " ++ show tm
    () <- putStrLn $ "args       : " ++ show args
    () <- putStrLn $ "id         : " ++ show nf
    () <- putStrLn $ "1 + 1      : " ++ show two
    () <- putStrLn $ "2          : " ++ show (suc one)
    () <- putStrLn $ "4          : " ++ show (suc $ suc two)
    () <- putStrLn $ "(1 + 1) * 2: " ++ show four
    return ()
