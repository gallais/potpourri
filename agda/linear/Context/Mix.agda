module linear.Context.Mix where

open import Data.Vec as V hiding (_∷ʳ_ ; fromList)
open import linear.Context
import linear.Usage.Erasure as UE

data _++_≅_ : ∀ {m n p} → Context m → Context n → Context p → Set where
  [] : [] ++ [] ≅ []
  _∷ˡ_ : ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p}
         σ → γ ++ δ ≅ θ → (σ ∷ γ) ++ δ ≅ (σ ∷ θ)
  _∷ʳ_ : ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p}
         σ → γ ++ δ ≅ θ → γ ++ (σ ∷ δ) ≅ (σ ∷ θ)

infix 2 _++_≅_
_++ˡ_ : ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p}
          {o} (φ : Context o) → γ ++ δ ≅ θ → φ V.++ γ ++ δ ≅ φ V.++ θ
[]      ++ˡ p = p
(σ ∷ φ) ++ˡ p = σ ∷ˡ (φ ++ˡ p)

fromList : ∀ {γ δ θ} → γ UE.++ δ ≅ θ → V.fromList γ ++ V.fromList δ ≅ V.fromList θ
fromList UE.[]       = []
fromList (σ UE.∷ˡ p) = σ ∷ˡ fromList p
fromList (σ UE.∷ʳ p) = σ ∷ʳ fromList p
