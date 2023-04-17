{-# OPTIONS --without-K --safe #-}

module Coverage where

open import Data.Unit.Base
open import Data.Empty
open import Data.Sum.Base
open import Data.Product
open import Data.Maybe.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality


data Desc : Set where
  `⊤ : Desc
  _`+_ _`×_ : (d₁ d₂ : Desc) → Desc
  `X : Desc

⟦_⟧ : Desc → Set → Set
⟦ `⊤       ⟧ X = ⊤
⟦ d₁ `+ d₂ ⟧ X = ⟦ d₁ ⟧ X ⊎ ⟦ d₂ ⟧ X
⟦ d₁ `× d₂ ⟧ X = ⟦ d₁ ⟧ X × ⟦ d₂ ⟧ X
⟦ `X       ⟧ X = X

data `μ (d : Desc) : Set where
  ‵in : ⟦ d ⟧ (`μ d) → `μ d

data μPat (d : Desc) : Set
data Pat (d : Desc) : (e : Desc) → Set

data μPat d where
  `var : μPat d
  `in : Pat d d → μPat d

data Pat d where
  `var : ∀ {e} → Pat d e
  `tt : Pat d `⊤
  `inj₁ : ∀ {e₁ e₂} → Pat d e₁ → Pat d (e₁ `+ e₂)
  `inj₂ : ∀ {e₁ e₂} → Pat d e₂ → Pat d (e₁ `+ e₂)
  _`,_ : ∀ {e₁ e₂} → Pat d e₁ → Pat d e₂ → Pat d (e₁ `× e₂)
  `rec : μPat d → Pat d `X


module _ (ini d : Desc) where

  Sound : (partition : Desc × Maybe Desc) → Set
  Sound (t , nothing) = Pat ini t → Pat ini d
  Sound (t , just l) = Pat ini t ⊎ Pat ini l → Pat ini d

  Complete : (partition : Desc × Maybe Desc) (sound : Sound partition) → Set
  Complete (t , nothing) sound = (p : Pat ini d) → Σ[ p′ ∈ Pat ini t ] p ≡ sound p′
  Complete (t , just l) sound
    = (p : Pat ini d)
    → Σ[ p′ ∈ Pat ini t ] p ≡ sound (inj₁ p′)
    ⊎ Σ[ p′ ∈ Pat ini l ] p ≡ sound (inj₂ p′)

  record Split : Set where
    constructor mkSplit
    field
      partition : Desc × Maybe Desc
      sound     : Sound partition
      complete  : Complete partition sound
  open Split

_\\_ : ∀ {ini} (d : Desc) (p : Pat ini d) →
       Split ini d
d \\ `var = record
  { partition = d , nothing
  ; sound = λ p → p
  ; complete = λ p → p , refl }
`⊤ \\ `tt = record
  { partition = _ , nothing
  ; sound = λ p → p
  ; complete = λ p → p , refl }
(d₁ `+ d₂) \\ `inj₁ p with d₁ \\ p
... | mkSplit (t , nothing) sound complete = {!!}
... | mkSplit (t , just l) sound complete = {!!}
(d₁ `+ d₂) \\ `inj₂ p = {!!}
(d₁ `× d₂) \\ (p `, p₁) = {!!}
`X \\ `rec x = {!!}


{-
split : ∀ {ini} d (p : Pat ini d) → Split ini d

spl \\ p with complete spl p
... | inj₁ (p′ , refl) = fail p′
... | inj₂ (p′ , eq) = {!!}

split d `var = record
  { taken = d
  ; leftover = `⊥
  ; sound = [ id , absurd ]′
  ; complete = λ p → inj₁ (p , refl) }
split `⊤ `tt = record
  { taken = `⊤
  ; leftover = `⊥
  ; sound = [ id , absurd ]′
  ; complete = λ p → inj₁ (p , refl) }
split (d₁ `+ d₂) (`inj₁ p) = let spl′ = split d₁ p in record
  { taken = taken spl′ `+ `⊥
  ; leftover = leftover spl′ `+ d₂
  ; sound = [ (λ where
                   `var → `var
                   (`inj₁ p′) → `inj₁ (sound spl′ (inj₁ p′))
                   (`inj₂ p′) → absurd p′)
            , (λ where
                   `var → `var
                   (`inj₁ p′) → `inj₁ (sound spl′ (inj₂ p′))
                   (`inj₂ p′) → `inj₂ p′)
            ]′
  ; complete = λ where
     `var → {!!}
     (`inj₁ p) → {!!}
     (`inj₂ p) → inj₂ (`inj₂ p , refl)
  }
split (d₁ `+ d₂) (`inj₂ p) = {!!}
split (d₁ `× d₂) (p `, q) = {!!}
split `X (`rec x) = {!!}
-}
