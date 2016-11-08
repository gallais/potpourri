module Section3.Core where

open import Data.Nat
import Data.Integer as ℤ
open import Data.Bool
open import Data.Product
open import Data.List
open import Data.String as String
open import Function

import Section2.Core as S2

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
  []    : ∀ {b} → Doc b
  _<>_  : ∀ {b} → Doc b → Doc b → Doc b
  txt   : ∀ {b} → String → Doc b
  _>>_  : ∀ {b} → ℕ → Doc b → Doc b
  ln    : ∀ {b} → Doc b
  _<|>_ : ∀ {b c} → Doc b → Doc c → Doc true

press : Press (Doc true)
press = record
  { _<>_   = _<>_
  ; ε      = []
  ; text   = txt
  ; line   = ln
  ; nest   = _>>_
  ; group  = group
  ; layout = layout
  } where

  flatten : ∀ {b} → Doc b → Doc false
  flatten []        = []
  flatten (d <> e)  = flatten d <> flatten e
  flatten (txt s)   = txt s
  flatten (n >> d)  = flatten d
  flatten ln        = txt " "
  flatten (d <|> e) = flatten d

  group : ∀ {b} → Doc b → Doc true
  group d = flatten d <|> d

  best : ∀ {b} → ℕ → Doc b → S2.Doc false
  best w d = go w 0 0 d $ λ _ → S2.[] where

    go : ∀ {b} → ℕ → ℕ → ℕ → Doc b → (ℕ → S2.Doc false) → S2.Doc false
    go w k i []        ds = ds k
    go w k i (d <> e)  ds = go w k i d $ λ k → go w k i e ds
    go w k i (txt s)   ds = s S2.<< ds (k + length (toList s))
    go w k i (n >> d)  ds = go w k (i + n) d ds
    go w k i ln        ds = i S2.vv ds i
    go w k i (d <|> e) ds = better w k (go w k i d ds) (go w k i e ds)
      where open S2.pressImplementation using (better)

  layout : ℕ → Doc true → String
  layout w d = S2.pressImplementation.layout $ best w d
