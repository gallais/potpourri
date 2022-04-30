{-# OPTIONS --safe --without-K #-}

open import Data.Sum.Base

data Desc : Set₁ where
  `X : Desc
  `κ : Set → Desc
  _`+_ : Desc → Desc → Desc

⟦_⟧ : Desc → Set → Set
⟦ `X     ⟧ X = X
⟦ `κ A   ⟧ X = A
⟦ d `+ e ⟧ X = ⟦ d ⟧ X ⊎ ⟦ e ⟧ X

{-
module FAILING where

  data `μ (d : Desc) : Set where
    mk : ⟦ d ⟧ (`μ d) → `μ d

  module _ {d} {X} (φ : ⟦ d ⟧ X → X) where

    fold : `μ d → X
    fold' : ∀ e → ⟦ e ⟧ (`μ d) → ⟦ e ⟧ X

    fold (mk t) = φ (fold' d t)

    fold' `X       t = fold t
    fold' (`κ A)   t = t
    fold' (e `+ f) t = map (fold' e) (fold' f) t
-}

data `μ (d : Desc) : (e : Desc) → Set₁ where
  mkX  : `μ d d → `μ d `X
  mkκ  : ∀ {A} → A → `μ d (`κ A)
  inj₁ : ∀ {e f} → `μ d e → `μ d (e `+ f)
  inj₂ : ∀ {e f} → `μ d f → `μ d (e `+ f)

module _ {d} {X} (φ : ⟦ d ⟧ X → X) where

  fold : `μ d d → X
  fold' : ∀ e → `μ d e → ⟦ e ⟧ X

  fold t = φ (fold' d t)

  fold' `X       (mkX t)  = fold t
  fold' (`κ A)   (mkκ a)  = a
  fold' (e `+ f) (inj₁ t) = inj₁ (fold' e t)
  fold' (e `+ f) (inj₂ t) = inj₂ (fold' f t)
