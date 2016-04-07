module linear.Usage.Consumption where

open import Data.Nat
open import Data.Vec hiding (map ; [_] ; split ; _++_)
open import Data.Product hiding (swap)
open import Function

open import linear.Type
open import linear.Context hiding (_++_)
open import linear.Usage as U hiding (_++_)
import Relation.Binary.PropositionalEquality as PEq

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

antisym : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} → Γ ⊆ Δ → Δ ⊆ Γ → Γ PEq.≡ Δ
antisym []      []     = PEq.refl
antisym (─∷ p)  (─∷ q) = PEq.cong _ $ antisym p q
antisym (a ∷ p) ()

infixr 3 _++_
_++_ : {m n : ℕ} {γ : Context m} {δ : Context n} {Γ Δ θ ξ : Usages γ} {χ Φ : Usages δ} →
       χ ⊆ Φ → Γ ─ Δ ≡ θ ─ ξ → χ U.++ Γ ─ Φ U.++ Δ ≡ χ U.++ θ ─ Φ U.++ ξ
[]    ++ q = q
─∷ p  ++ q = ─∷ (p ++ q)
a ∷ p ++ q = a ∷ (p ++ q)

swap : {n : ℕ} {γ : Context n} {Γ Δ θ : Usages γ} → Γ ⊆ Δ → Δ ⊆ θ →
       ∃ λ Δ′ → Γ ─ Δ ≡ Δ′ ─ θ × Δ ─ θ ≡ Γ ─ Δ′
swap []      []      = [] , [] , []
swap (─∷ p)  (─∷ q)  = map _ (map ─∷_    ─∷_)    $ swap p q
swap (─∷ p)  (a ∷ q) = map _ (map ─∷_    (a ∷_)) $ swap p q
swap (a ∷ p) (─∷ q)  = map _ (map (a ∷_) ─∷_)    $ swap p q

split : {m n : ℕ} {γ : Context m} {δ : Context n} (Γ₁ Γ₂ : Usages γ) {Δ₁ Δ₂ : Usages δ} →
        Γ₁ U.++ Δ₁ ⊆ Γ₂ U.++ Δ₂ → Γ₁ ⊆ Γ₂ × Δ₁ ⊆ Δ₂
split []      []      p       = [] , p
split (_ ∷ _) (_ ∷ _) (─∷ p)  = map ─∷_    id $ split _ _ p
split (_ ∷ _) (_ ∷ _) (a ∷ p) = map (a ∷_) id $ split _ _ p

truncate : {m n : ℕ} (γ : Context m) {δ : Context n} {Δ₁ Δ₂ : Usages δ} →
           [[ γ ]] U.++ Δ₁ ⊆ ]] γ [[ U.++ Δ₂ → Δ₁ ⊆ Δ₂
truncate γ = proj₂ ∘ split [[ γ ]] ]] γ [[

divide : {n : ℕ} {γ : Context n} {Γ Δ θ ξ χ : Usages γ} → Γ ─ Δ ≡ θ ─ ξ → Γ ⊆ χ → χ ⊆ Δ →
        ∃ λ Φ → Γ ─ χ ≡ θ ─ Φ × χ ─ Δ ≡ Φ ─ ξ
divide []       []       []       = [] , [] , []
divide (a ∷ eq) (─∷ p)   (.a ∷ q) = map _ (map ─∷_    (a ∷_)) $ divide eq p q
divide (a ∷ eq) (.a ∷ p) (─∷ q)   = map _ (map (a ∷_) ─∷_)    $ divide eq p q
divide (─∷ eq)  (─∷ p)   (─∷ q)   = map _ (map ─∷_    ─∷_)    $ divide eq p q
divide (─∷ eq)  (a ∷ p)  ()

equality : {n : ℕ} {γ : Context n} {Γ θ ξ : Usages γ} → Γ ─ Γ ≡ θ ─ ξ → θ PEq.≡ ξ
equality []     = PEq.refl
equality (─∷ p) = PEq.cong _ $ equality p

Consumption : {T : ℕ → Set} (𝓣 : Typing T) → Set
Consumption {T} 𝓣 = {n : ℕ} {γ : Context n} {t : T n} {A : Type} {Γ Δ : Usages γ} → 𝓣 Γ t A Δ → Γ ⊆ Δ

Framing : {T : ℕ → Set} (𝓣 : Typing T) → Set
Framing {T} 𝓣 =
  {n : ℕ} {γ : Context n} {Γ Δ θ ξ : Usages γ} {t : T n} {A : Type} →
  Γ ─ Δ ≡ θ ─ ξ → 𝓣 Γ t A Δ → 𝓣 θ t A ξ

consumptionFin : Consumption TFin
consumptionFin z     = _ ∷ refl _
consumptionFin (s k) = ─∷ consumptionFin k

framingFin : Framing TFin
framingFin (A ∷ p) z rewrite equality p = z
framingFin (─∷ p) (s k) = s framingFin p k
