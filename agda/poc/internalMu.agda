module internalMu where

open import Level using (Level)
open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Data.Unit
open import Data.Product
open import Function

Fin-case : {ℓ : Level} {n : ℕ} {P : Fin (suc n) → Set ℓ}
           (p0 : P zero) (pS : (k : Fin n) → P (suc k)) →
           (k : Fin (suc n)) → P k
Fin-case p0 pS zero    = p0
Fin-case p0 pS (suc k) = pS k

Fin0-elim : {ℓ : Level} {A : Set ℓ} (hf : Fin 0) → A
Fin0-elim ()

data Desc (n : ℕ) : Set₁ where
  `μ : (d : Desc (suc n)) → Desc n
  `r : (k : Fin n) (d : Desc n) → Desc n
  `σ : (A : Set) (d : A → Desc n) → Desc n
  `π : (A : Set) (d : A → Desc n) → Desc n
  `■ : Desc n

mutual

  ⟦_⟧_ : {n : ℕ} (d : Desc n) (ρ : Fin n → Set) → Set
  ⟦ `μ d   ⟧ ρ = μ d ρ
  ⟦ `r k d ⟧ ρ = ρ k × ⟦ d ⟧ ρ
  ⟦ `σ A d ⟧ ρ = Σ[ a ∈ A ] ⟦ d a ⟧ ρ
  ⟦ `π A d ⟧ ρ = (a : A) → ⟦ d a ⟧ ρ
  ⟦ `■     ⟧ ρ = ⊤

  data μ {n : ℕ} (d : Desc (suc n)) (ρ : Fin n → Set) : Set where
    ⟨_⟩ : ⟦ d ⟧ Fin-case (μ d ρ) ρ → μ d ρ

listDesc : {n : ℕ} (k : Fin n) → Desc n
listDesc k =
  `μ $ `σ Bool $ λ isNil →
       case isNil of λ
         { true  → `■
         ; false → `r (suc k) (`r (# 0) `■)
         }

rosetreeDesc : Desc 0
rosetreeDesc = `μ $ listDesc $ # 0

rosetree : Set
rosetree = ⟦ rosetreeDesc ⟧ Fin0-elim

nil : {ρ : _} → ⟦ listDesc {1} (# 0) ⟧ ρ
nil = ⟨ true , tt ⟩

cons : {ρ : _} → ρ zero → ⟦ listDesc {1} (# 0) ⟧ ρ → ⟦ listDesc {1} (# 0) ⟧ ρ
cons x xs = ⟨ false , x , xs , tt ⟩

leaf : rosetree
leaf = ⟨ ⟨ true , tt ⟩ ⟩

node : ⟦ listDesc {1} (# 0) ⟧ (Fin-case rosetree Fin0-elim) → rosetree
node ts = ⟨ ts ⟩

example : rosetree
example = node $ cons t₁ $ cons t₂ nil
  where t₁ : rosetree
        t₁ = node nil
        t₂ : rosetree
        t₂ = node $ cons t₁ $ cons t₁ nil
