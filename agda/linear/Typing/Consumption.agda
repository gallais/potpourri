module linear.Typing.Consumption where

open import Data.Nat
open import Data.Vec
open import Function

open import linear.Type
open import linear.Context
open import linear.Typing
open import linear.Usage hiding ([_])
open import linear.Usage.Consumption

mutual

  consumptionInfer : Consumption TInfer
  consumptionInfer (`var k)                     = consumptionFin k
  consumptionInfer (`app t u)                   = trans (consumptionInfer t) (consumptionCheck u)
  consumptionInfer (`case t return σ of l %% r) =
    trans (consumptionInfer t) $ truncate [ _ ] $ consumptionCheck l
  consumptionInfer (`cut t)                     = consumptionCheck t

  consumptionCheck : Consumption TCheck
  consumptionCheck (`lam t)            = truncate [ _ ] $ consumptionCheck t
  consumptionCheck (`let p ∷= t `in u) =
    trans (consumptionInfer t) $ truncate (patternContext p) $ consumptionCheck u
  consumptionCheck (`prd a b)          = trans (consumptionCheck a) (consumptionCheck b)
  consumptionCheck (`inl t)            = consumptionCheck t
  consumptionCheck (`inr t)            = consumptionCheck t
  consumptionCheck (`neu t)            = consumptionInfer t
