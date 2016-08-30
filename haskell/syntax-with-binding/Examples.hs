{-# OPTIONS -Wall                  #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Examples where

import GHC.TypeLits
import Data.Void

import Utils
import Generic
import Syntaxes

-------------------------------------------------------------
-- OPEN TERMS WITH N FREE VARIABLES
-------------------------------------------------------------

type family Free (n :: Nat) :: * where
  Free 0 = Void
  Free n = Maybe (Free (n - 1))

type OCase n = Case (Free n)
type OTerm n = Term (Free n)

-------------------------------------------------------------
-- EXAMPLES FOR TmF
-------------------------------------------------------------

oTERM :: OTerm 1
oTERM = TmL $ Var $ Just Nothing

oTERM' :: OTerm 2
oTERM' = rename oTERM Just

idTERM :: Term Void
idTERM = TmL $ Var Nothing

falseTERM :: Term Void
falseTERM = subst oTERM $ maybe idTERM absurd

cutTERM :: Term Void
cutTERM = TmA falseTERM falseTERM -- (\ x y -> y) (\ x y -> y) ---->* (\ y -> y)

normTERM :: Term Void
normTERM = norm cutTERM

-------------------------------------------------------------
-- EXAMPLES FOR CsF
-------------------------------------------------------------

oCASE :: OCase 1
oCASE = CsCA (Var Nothing) $ Pair (Var (Just Nothing), Var Nothing)
  -- Either a (Either a b) -> Either a b

oCASE' :: OCase 4
oCASE' = rename oCASE $ Just . Just . Just

-- Representing natural numbers in Case
-- Defining addition by a fix point

natToCase :: Integer -> Case a
natToCase n | n <= 0 = CsLI CsUN
natToCase n          = CsRI $ natToCase (n - 1)

caseToNat :: Case a -> Integer
caseToNat t = case t of
  CsLI CsUN -> 0
  CsRI n    -> 1 + caseToNat n
  _         -> error "Malformed Nat"

plus :: Case a
plus =
  CsLA               $ {- m  -}
  CsFX               $ {- m+ -}
  CsLA               $ {- n  -}
  CsCA (Var Nothing) $ {- case n -}
  Pair
  ( Var (Just (Just (Just Nothing)))
  , (CsRI $ Var (Just (Just Nothing)) $$ Var Nothing)
  )

five :: Integer
five = caseToNat $ norm $ plus $$ natToCase 2 $$ natToCase 3

mult :: Case a
mult =
  CsLA               $ {- m  -}
  CsFX               $ {- m* -}
  CsLA               $ {- n  -}
  CsCA (Var Nothing) $ {- case n -}
  Pair
  ( CsLI CsUN
  , (plus $$ (Var (Just (Just (Just Nothing))))
          $$ (Var (Just (Just Nothing)) $$ Var Nothing))
  )

ten :: Integer
ten = caseToNat $ norm $ mult $$ natToCase five $$ natToCase 2
