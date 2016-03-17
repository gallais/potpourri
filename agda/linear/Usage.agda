module linear.Usage where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_])

open import linear.Type
open import linear.Context

data Usage : (a : Type) → Set where
  [_] : (a : Type) → Usage a
  ]_[ : (a : Type) → Usage a

infixl 10 _∙_
data Usages : {n : ℕ} (γ : Context n) → Set where
  []  : Usages []
  _∷_ : {n : ℕ} {γ : Context n} {a : Type} → Usage a → Usages γ → Usages (a ∷ γ)

data HoleyUsages {m : ℕ} : {n : ℕ} (h : Holey m n) → Set where
  []  : HoleyUsages []
  _∷_ : {n : ℕ} {h : Holey m n} {a : Type} → HoleyUsages h → Usage a → HoleyUsages (a ∷ h)
  _∙_ : {n o : ℕ} {g : Holey m n} {h : Holey n o} → HoleyUsages g → HoleyUsages h → HoleyUsages (g ∙ h)

[[_]]++_ : {m n : ℕ} {γ : Context m} (δ : Context n) (Γ : Usages γ) → Usages (δ ++ γ)
[[ δ ]]++ Γ = induction (λ δ → Usages (δ ++ _)) Γ (λ a Γ → [ a ] ∷_) δ

]]_[[++_ : {m n : ℕ} {γ : Context m} (δ : Context n) (Γ : Usages γ) → Usages (δ ++ γ)
]] δ [[++ Γ = induction (λ δ → Usages (δ ++ _)) Γ (λ a Γ → ] a [ ∷_) δ

infix 1 _⊢_∈[_]⊠_
data _⊢_∈[_]⊠_ : {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) (a : Type) (Δ : Usages γ) → Set where
  z : {n : ℕ} {γ : Context n} {Γ : Usages γ} {a : Type} → [ a ] ∷ Γ ⊢ zero ∈[ a ]⊠ ] a [ ∷ Γ
  s_ : {n : ℕ} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ} {a b : Type} {u : Usage b} →
       Γ ⊢ k ∈[ a ]⊠ Δ → u ∷ Γ ⊢ suc k ∈[ a ]⊠ u ∷ Δ
