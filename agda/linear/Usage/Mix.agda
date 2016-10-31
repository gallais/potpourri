module linear.Usage.Mix where

open import Data.Product as Prod
open import Data.Vec as V hiding ([_] ; _∷ʳ_ ; fromList)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import linear.Context
open import linear.Context.Mix as CM hiding (_++ˡ_)
open import linear.Usage as U hiding ([_])
import linear.Usage.Erasure as UE

infix 2 [_]_++_≅_ 
data [_]_++_≅_ : ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p} →
                 γ ++ δ ≅ θ → Usages γ → Usages δ → Usages θ → Set where
  []   : [ [] ] [] ++ [] ≅ []
  _∷ˡ_ : ∀ {m n p σ} {γ : Context m} {δ : Context n} {θ : Context p}
         {p : γ ++ δ ≅ θ} {Γ Δ Θ} (S : Usage σ) →
         [ p ] Γ ++ Δ ≅ Θ → [ σ ∷ˡ p ] S ∷ Γ ++ Δ ≅ S ∷ Θ
  _∷ʳ_ : ∀ {m n p σ} {γ : Context m} {δ : Context n} {θ : Context p}
         {p : γ ++ δ ≅ θ} {Γ Δ Θ} (S : Usage σ) →
         [ p ] Γ ++ Δ ≅ Θ → [ σ ∷ʳ p ] Γ ++ S ∷ Δ ≅ S ∷ Θ

≅-inj : ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p}
  {Γ₁ Γ₂ Δ₁ Δ₂ Θ} (p : γ ++ δ ≅ θ) →
  [ p ] Γ₁ ++ Δ₁ ≅ Θ → [ p ] Γ₂ ++ Δ₂ ≅ Θ →
  Γ₁ ≡ Γ₂ × Δ₁ ≡ Δ₂
≅-inj []       []         []          = refl , refl
≅-inj (a ∷ˡ p) (S ∷ˡ eq₁) (.S ∷ˡ eq₂) = Prod.map (cong (S ∷_)) id $ ≅-inj p eq₁ eq₂
≅-inj (σ ∷ʳ p) (S ∷ʳ eq₁) (.S ∷ʳ eq₂) = Prod.map id (cong (S ∷_)) $ ≅-inj p eq₁ eq₂

_++ˡ_ : ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p}
        {p : γ ++ δ ≅ θ} {Γ Δ Θ} {o} {φ : Context o} (Φ : Usages φ) →
  [ p ] Γ ++ Δ ≅ Θ → [ φ CM.++ˡ p ] Φ U.++ Γ ++ Δ ≅ Φ U.++ Θ
[]      ++ˡ eq = eq
(S ∷ Φ) ++ˡ eq = S ∷ˡ (Φ ++ˡ eq)

[[fromList]] : ∀ {γ δ θ} (p : γ UE.++ δ ≅ θ) →
               [ CM.fromList p ] [[ _ ]] ++ [[ _ ]] ≅ [[ V.fromList θ ]]
[[fromList]] UE.[]       = []
[[fromList]] (a UE.∷ˡ p) = U.[ a ] ∷ˡ [[fromList]] p
[[fromList]] (a UE.∷ʳ p) = U.[ a ] ∷ʳ [[fromList]] p


]]fromList[[ : ∀ {γ δ θ} (p : γ UE.++ δ ≅ θ) →
               [ CM.fromList p ] ]] _ [[ ++ ]] _ [[ ≅ ]] V.fromList θ [[
]]fromList[[ UE.[]       = []
]]fromList[[ (a UE.∷ˡ p) = ] a [ ∷ˡ ]]fromList[[ p
]]fromList[[ (a UE.∷ʳ p) = ] a [ ∷ʳ ]]fromList[[ p
