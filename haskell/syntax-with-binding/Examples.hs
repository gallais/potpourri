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
oTERM = TmL' $ MkVar $ Just Nothing

oTERM' :: OTerm 2
oTERM' = rename oTERM (fmap Just)

idTERM :: Term Void
idTERM = TmL' $ MkVar Nothing

falseTERM :: Term Void
falseTERM = subst oTERM $ maybe idTERM absurd . runVariable

cutTERM :: Term Void
cutTERM = TmA falseTERM falseTERM -- (\ x y -> y) (\ x y -> y) ---->* (\ y -> y)

normTERM :: Term Void
normTERM = norm cutTERM

-------------------------------------------------------------
-- EXAMPLES FOR CsF
-------------------------------------------------------------

oCASE :: OCase 1
oCASE = CsCA' (MkVar Nothing) $ Pair (MkVar (Just Nothing), MkVar Nothing)
  -- Either a (Either a b) -> Either a b

oCASE' :: OCase 4
oCASE' = rename oCASE $ fmap (Just . Just . Just)

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
  CsLA'                 $ {- m  -}
  CsFX'                 $ {- m+ -}
  CsLA'                 $ {- n  -}
  CsCA' (MkVar Nothing) $ {- case n -}
  Pair
  ( MkVar (Just (Just (Just Nothing)))
  , (CsRI $ MkVar (Just (Just Nothing)) $$ MkVar Nothing)
  )

five :: Integer
five = caseToNat $ norm $ plus $$ natToCase 2 $$ natToCase 3

mult :: Case a
mult =
  CsLA'                 $ {- m  -}
  CsFX'                 $ {- m* -}
  CsLA'                 $ {- n  -}
  CsCA' (MkVar Nothing) $ {- case n -}
  Pair
  ( CsLI CsUN
  , (plus $$ (MkVar (Just (Just (Just Nothing))))
          $$ (MkVar (Just (Just Nothing)) $$ MkVar Nothing))
  )

ten :: Integer
ten = caseToNat $ norm $ mult $$ natToCase five $$ natToCase 2

-------------------------------------------------------------
-- EXAMPLES FOR CLF
-------------------------------------------------------------

ones :: CList Integer
ones = CList $ CLCON' 1 $ Var Z

ones' :: [Integer]
ones' = take 10 $ toStream ones

twothrees :: CList Integer
twothrees = CList $ CLCON' 2 $ CLCON' 3 $ Var $ S Z

twothrees' :: [Integer]
twothrees' = take 10 $ toStream twothrees

threefours :: CList Integer
threefours = fmap (+1) twothrees

threefours' :: [Integer]
threefours' = take 10 $ toStream threefours
