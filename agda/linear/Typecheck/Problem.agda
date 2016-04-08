module linear.Typecheck.Problem where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (_++_ ; tail)
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import linear.Type
open import linear.Context as C hiding (_++_)
open import linear.Usage
open import linear.Language
open import linear.Typing
open import linear.RawIso

-- The Typechecking problems we are going to prove are decidable
record CONSUME {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) : Set where
  constructor _,_,_
  field
    type   : Type
    usages : Usages γ
    proof  : Γ ⊢ k ∈[ type ]⊠ usages

infix 4 _,_,_
record INFER {n : ℕ} {γ : Context n} (Γ : Usages γ) (t : Infer n) : Set where
  constructor _,_,_
  field
    type   : Type
    usages : Usages γ
    proof  : Γ ⊢ t ∈ type ⊠ usages

infix 4 _,_
record CHECK {n : ℕ} {γ : Context n} (Γ : Usages γ) (σ : Type) (t : Check n) : Set where
  constructor _,_
  field
    usages : Usages γ
    proof  : Γ ⊢ σ ∋ t ⊠ usages

record PATTERN {n : ℕ} (σ : Type) (p : Pattern n) : Set where
  constructor _,_
  field
    context : Context n
    proof   : σ ∋ p ↝ context

record TRUNCATE {n o : ℕ} {γ : Context n} (δ : Context o) (Γ : Usages (δ C.++ γ)) : Set where
  constructor _,_
  field
    usages : Usages γ
    proof  : Γ ≡ (]] δ [[ ++ usages)


-- some related RawIsos
consumeSuc : {n : ℕ} {γ : Context n} (Γ : Usages γ) {σ : Type} (a : Usage σ) (k : Fin n) →
             RawIso (CONSUME Γ k) (CONSUME (a ∷ Γ) (suc k))
push (consumeSuc Γ a k) (σ , Δ        , v)     = σ , (a ∷ Δ) , s v
pull (consumeSuc Γ a k) (σ , (.a ∷ Δ) , (s v)) = σ , Δ , v

truncateUsed : {n o : ℕ} {γ : Context n} {a : Type} (δ : Context o) (ΔΓ : Usages (δ C.++ γ)) →
               RawIso (TRUNCATE δ ΔΓ) (TRUNCATE (a ∷ δ) (] a [ ∷ ΔΓ))
push (truncateUsed δ ΔΓ) (Γ , prf) = _ , cong (_ ∷_) prf
pull (truncateUsed δ ΔΓ) (Γ , prf) = _ , cong tail prf

inferVar : {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) → RawIso (CONSUME Γ k) (INFER Γ (`var k))
push (inferVar Γ k) (σ , Δ , v)      = σ , Δ , `var v
pull (inferVar Γ k) (σ , Δ , `var v) = σ , Δ , v

inferCut : {n : ℕ} {γ : Context n} (Γ : Usages γ) (t : Check n) (σ : Type) →
           RawIso (CHECK Γ σ t) (INFER Γ (`cut t σ))
push (inferCut Γ t σ) (Δ , p)           = σ , Δ , `cut p
pull (inferCut Γ t σ) (.σ , Δ , `cut p) = Δ , p

checkInl : {n : ℕ} {γ : Context n} (Γ : Usages γ) (t : Check n) (σ τ : Type) →
           RawIso (CHECK Γ σ t) (CHECK Γ (σ ⊕ τ) (`inl t))
push (checkInl Γ t σ τ) (Δ , p)      = _ , `inl p
pull (checkInl Γ t σ τ) (Δ , `inl p) = _ , p

checkInr : {n : ℕ} {γ : Context n} (Γ : Usages γ) (t : Check n) (σ τ : Type) →
           RawIso (CHECK Γ τ t) (CHECK Γ (σ ⊕ τ) (`inr t))
push (checkInr Γ t σ τ) (Δ , p)      = _ , `inr p
pull (checkInr Γ t σ τ) (Δ , `inr p) = _ , p

patternTensor : {m n : ℕ} {p : Pattern m} {q : Pattern n} {σ τ : Type} →
                 RawIso (PATTERN σ p × PATTERN τ q) (PATTERN (σ ⊗ τ) (p ,, q))
push patternTensor ((_ , p) , (_ , q)) = _ , p ,, q
pull patternTensor (_ , p ,, q)        = (_ , p) , (_ , q)
