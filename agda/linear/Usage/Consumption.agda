module linear.Usage.Consumption where

open import Data.Nat
open import Data.Vec hiding (map ; [_] ; split ; _++_)
open import Data.Product hiding (swap)
open import Function

open import linear.Type
open import linear.Context hiding (_++_)
open import linear.Usage

infix 3 _─_≡_─_
data _─_≡_─_ : {n : ℕ} {γ : Context n} (Γ Δ θ ξ : Usages γ) → Set where
  []  : [] ─ [] ≡ [] ─ []
  ─∷_ : {n : ℕ} {γ : Context n} {Γ Δ θ ξ : Usages γ} {a : Type} {A B : Usage a} →
        Γ ─ Δ ≡ θ ─ ξ → A ∷ Γ ─ A ∷ Δ ≡ B ∷ θ ─ B ∷ ξ
  _∷_ : {n : ℕ} {γ : Context n} {Γ Δ θ ξ : Usages γ} (a : Type) →
        Γ ─ Δ ≡ θ ─ ξ → [ a ] ∷ Γ ─ ] a [ ∷ Δ ≡ [ a ] ∷ θ ─ ] a [ ∷ ξ

infix 3 _⊆_
_⊆_ : {n : ℕ} {γ : Context n} (Γ Δ : Usages γ) → Set
Γ ⊆ Δ = Γ ─ Δ ≡ Γ ─ Δ

pure : {n : ℕ} (γ : Context n) → [[ γ ]] ⊆ ]] γ [[
pure []      = []
pure (a ∷ γ) = a ∷ pure γ

refl : {n : ℕ} {γ : Context n} (Γ : Usages γ) → Γ ⊆ Γ
refl []      = []
refl (_ ∷ Γ) = ─∷ refl Γ

trans : {n : ℕ} {γ : Context n} {Γ Δ θ : Usages γ} → Γ ⊆ Δ → Δ ⊆ θ → Γ ⊆ θ
trans []      []      = []
trans (─∷ p)  (─∷ q)  = ─∷ trans p q
trans (a ∷ p) (─∷ q)  = a ∷ trans p q
trans (─∷ p)  (a ∷ q) = a ∷ trans p q

swap : {n : ℕ} {γ : Context n} {Γ Δ θ : Usages γ} → Γ ⊆ Δ → Δ ⊆ θ →
       ∃ λ Δ′ → Γ ─ Δ ≡ Δ′ ─ θ × Δ ─ θ ≡ Γ ─ Δ′
swap []      []      = [] , [] , []
swap (─∷ p)  (─∷ q)  = map _ (map ─∷_    ─∷_)    $ swap p q
swap (─∷ p)  (a ∷ q) = map _ (map ─∷_    (a ∷_)) $ swap p q
swap (a ∷ p) (─∷ q)  = map _ (map (a ∷_) ─∷_)    $ swap p q

split : {m n : ℕ} {γ : Context m} {δ : Context n} (Γ₁ Γ₂ : Usages γ) {Δ₁ Δ₂ : Usages δ} →
        Γ₁ ++ Δ₁ ⊆ Γ₂ ++ Δ₂ → Γ₁ ⊆ Γ₂ × Δ₁ ⊆ Δ₂
split []      []      p       = [] , p
split (_ ∷ _) (_ ∷ _) (─∷ p)  = map ─∷_    id $ split _ _ p
split (_ ∷ _) (_ ∷ _) (a ∷ p) = map (a ∷_) id $ split _ _ p

truncate : {m n : ℕ} (γ : Context m) {δ : Context n} {Δ₁ Δ₂ : Usages δ} →
           [[ γ ]] ++ Δ₁ ⊆ ]] γ [[ ++ Δ₂ → Δ₁ ⊆ Δ₂
truncate γ = proj₂ ∘ split [[ γ ]] ]] γ [[

divide : {n : ℕ} {γ : Context n} {Γ Δ θ ξ χ : Usages γ} → Γ ─ Δ ≡ θ ─ ξ → Γ ⊆ χ → χ ⊆ Δ →
        ∃ λ Φ → Γ ─ χ ≡ θ ─ Φ × χ ─ Δ ≡ Φ ─ ξ
divide []       []       []       = [] , [] , []
divide (a ∷ eq) (─∷ p)   (.a ∷ q) = map _ (map ─∷_    (a ∷_)) $ divide eq p q
divide (a ∷ eq) (.a ∷ p) (─∷ q)   = map _ (map (a ∷_) ─∷_)    $ divide eq p q
divide (─∷ eq)  (─∷ p)   (─∷ q)   = map _ (map ─∷_    ─∷_)    $ divide eq p q
divide (─∷ eq)  (a ∷ p)  ()

Consumption : {T : ℕ → Set} (𝓣 : Typing T) → Set
Consumption {T} 𝓣 = {n : ℕ} {γ : Context n} {t : T n} {A : Type} {Γ Δ : Usages γ} → 𝓣 Γ t A Δ → Γ ⊆ Δ

consumptionFin : Consumption TFin
consumptionFin z     = _ ∷ refl _
consumptionFin (s k) = ─∷ consumptionFin k
