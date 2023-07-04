module Data.Int64.Primitive where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String

infix 4 _==_
infixl 6 _+_ _-_

postulate
  Int64 : Set
  fromNat : Nat → Int64
  toNat : Int64 → Nat
  show : Int64 → String
  _+_ : Int64 → Int64 → Int64
  _-_ : Int64 → Int64 → Int64
  _==_ : Int64 → Int64 → Bool

{-# FOREIGN GHC import Data.Int #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC Int64 = type Int64 #-}
{-# COMPILE GHC fromNat = fromInteger #-}
{-# COMPILE GHC toNat = fromIntegral #-}
{-# COMPILE GHC show = T.pack . show #-}
{-# COMPILE GHC _+_ = (+) #-}
{-# COMPILE GHC _-_ = (-) #-}
{-# COMPILE GHC _==_ = (==) #-}
