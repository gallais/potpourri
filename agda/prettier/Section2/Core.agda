module Section2.Core where

open import Data.Nat
import Data.Integer as ℤ
open import Data.Bool
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
    group  : Doc → Doc
    layout : ℕ → Doc → String

infixr 4 _<|>_
data Doc : Bool → Set where
  []    : ∀ {b}   → Doc b
  _<<_  : ∀ {b}   → String → Doc b → Doc b
  _vv_  : ∀ {b}   → ℕ → Doc b → Doc b
  _<|>_ : ∀ {b c} → Doc b → Doc c → Doc true

press : Press (Doc true)
press = record
  { _<>_   = _<>_
  ; ε      = []
  ; text   = _<< []
  ; line   = 0 vv []
  ; nest   = nest
  ; group  = group
  ; layout = λ w → layout ∘ best w 0
  } module pressImplementation where

  forget : ∀ {b} → Doc b → Doc true
  forget []        = []
  forget (s << d)  = s << forget d
  forget (n vv d)  = n vv forget d
  forget (d <|> e) = d <|> e

  _<>_ : ∀ {b c} → Doc b → Doc c → Doc true
  []        <> e = forget e
  (s << d)  <> e = s << (d <> e)
  (n vv d)  <> e = n vv (d <> e)
  (l <|> r) <> e = (l <> e) <|> (r <> e)

  nest : ∀ {b} → ℕ → Doc b → Doc true
  nest k []        = []
  nest k (s << d)  = s << nest k d
  nest k (n vv d)  = (k + n) vv nest k d
  nest k (d <|> e) = nest k d <|> nest k e

  flatten : ∀ {b} → Doc b → Doc false
  flatten []        = []
  flatten (s << d)  = s << flatten d
  flatten (n vv d)  = " " << flatten d
  flatten (d <|> e) = flatten d

  group : ∀ {b} → Doc b → Doc true
  group []        = []
  group (s << d)  = s << group d
  group (n vv d)  = (" " << flatten d) <|> (n vv d)
  group (d <|> e) = group d <|> e

  fits : ℤ.ℤ → Doc false → Bool
  fits ℤ.-[1+ _ ] _ = false
  fits k []         = true
  fits k (s << d)   = fits (k ℤ.- ℤ.+ length (toList s)) d
  fits k (n vv d)   = true

  better : ℕ → ℕ → Doc false → Doc false → Doc false
  better w k d e = if fits (let open ℤ in + w - + k) d then d else e

  best : ∀ {b} → ℕ → ℕ → Doc b → Doc false
  best w k []        = []
  best w k (s << d)  = s << best w (k + length (toList s)) d
  best w k (n vv d)  = n vv best w n d
  best w k (d <|> e) = better w k (best w k d) (best w k e)

  layout : Doc false → String
  layout []       = ""
  layout (s << d) = s String.++ layout d
  layout (n vv d) = fromList ('\n' ∷ replicate n ' ') String.++ layout d
