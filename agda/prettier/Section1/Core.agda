module Section1.Core where

open import Data.Nat
open import Data.List
open import Data.String as String
open import Function

record Press {ℓ} (Doc : Set ℓ) : Set ℓ where
  infixr 5 _<>_
  field
    _<>_   : Doc → Doc → Doc
    ε      : Doc
    text   : String → Doc
    line   : Doc
    nest   : ℕ → Doc → Doc
    layout : Doc → String

data Doc : Set where
  []   :                Doc
  _<<_ : String → Doc → Doc
  _vv_ : ℕ      → Doc → Doc

press : Press Doc
press = record
  { _<>_   = _<>_
  ; ε      = []
  ; text   = _<< []
  ; line   = 0 vv []
  ; nest   = nest
  ; layout = layout
  } where

  _<>_ : Doc → Doc → Doc
  []       <> e = e
  (s << d) <> e = s << (d <> e)
  (n vv d) <> e = n vv (d <> e)

  nest : ℕ → Doc → Doc
  nest k []       = []
  nest k (s << d) = s << nest k d
  nest k (n vv d) = (k + n) vv nest k d

  layout : Doc → String
  layout []       = ""
  layout (s << d) = s String.++ layout d
  layout (n vv d) = fromList ('\n' ∷ replicate n ' ') String.++ layout d
