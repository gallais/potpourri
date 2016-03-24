module linear.Typing where

open import Data.Nat as ℕ
open import Data.Fin
open import Data.Vec hiding ([_] ; _++_)

open import linear.Type
open import linear.Scope as Sc hiding (Mergey ; copys)
open import linear.Context as C hiding (Mergey ; _⋈_ ; copys ; _++_ ; ++copys-elim)
open import linear.Language hiding (patternSize)
open import linear.Usage

infix 3 _⊢_∋_⊠_ _⊢_∈_⊠_ _∋_↝_
mutual
  
  data _⊢_∋_⊠_ {n : ℕ} {γ : Vec Type n} (Γ : Usages γ) : (A : Type) (t : Check n) (Δ : Usages γ) → Set where

    `lam_ : {σ τ : Type} {b : Check (suc n)} {Δ : Usages γ} →
    
             [ σ ] ∷ Γ ⊢ τ ∋ b ⊠ ] σ [ ∷ Δ →
           -------------------------
            Γ ⊢ σ ─o τ ∋ `lam b ⊠ Δ

    `let_∷=_`in_ : {σ τ : Type} {o : ℕ} {p : Pattern o} {δ : Vec Type o} {t : Infer n}
                  {Δ θ : Usages γ} {u : Check (o ℕ.+ n)} →

              σ ∋ p ↝ δ → Γ ⊢ t ∈ σ ⊠ Δ → [[ δ ]] ++ Δ ⊢ τ ∋ u ⊠ ]] δ [[ ++ θ →
            -----------------------------------------------------------------
                 Γ ⊢ τ ∋ `let p ∷= t `in u ⊠ θ

    `prd : {σ τ : Type} {a b : Check n} {Δ θ : Usages γ} →

             Γ ⊢ σ ∋ a ⊠ Δ → Δ ⊢ τ ∋ b ⊠ θ →
           ---------------------------------
             Γ ⊢ σ ⊗ τ ∋ `prd a b ⊠ θ

    `inl_ : {σ τ : Type} {t : Check n} {Δ : Usages γ} →

                  Γ ⊢ σ ∋ t ⊠ Δ →
           ---------------------------------
               Γ ⊢ σ ⊕ τ ∋ `inl t ⊠ Δ

    `inr_ : {σ τ : Type} {t : Check n} {Δ : Usages γ} →

                  Γ ⊢ τ ∋ t ⊠ Δ →
           ---------------------------------
               Γ ⊢ σ ⊕ τ ∋ `inr t ⊠ Δ

    `neu_ : {σ : Type} {t : Infer n} {Δ : Usages γ} →

             Γ ⊢ t ∈ σ ⊠ Δ →
           ---------------------
            Γ ⊢ σ ∋ `neu t ⊠ Δ
    
  data _⊢_∈_⊠_ {n : ℕ} {γ : Vec Type n} (Γ : Usages γ) : (t : Infer n) (A : Type) (Δ : Usages γ) → Set where

    `var : {σ : Type} {Δ : Usages γ} {k : Fin n} →

             Γ ⊢ k ∈[ σ ]⊠ Δ →
          ----------------------
            Γ ⊢ `var k ∈ σ ⊠ Δ
            
    `app : {σ τ : Type} {Δ θ : Usages γ} {t : Infer n} {u : Check n} →

            Γ ⊢ t ∈ σ ─o τ ⊠ Δ → Δ ⊢ σ ∋ u ⊠ θ →
          ---------------------------------------
             Γ ⊢ `app t u ∈ τ ⊠ θ            

    `case_return_of_%%_ : {σ τ : Type} {Δ θ : Usages γ} {t : Infer n} {l r : Check (suc n)} →

            Γ ⊢ t ∈ σ ⊕ τ ⊠ Δ →
            (ν : Type) →
            [ σ ] ∷ Δ ⊢ ν ∋ l ⊠ ] σ [ ∷ θ →
            [ τ ] ∷ Δ ⊢ ν ∋ r ⊠ ] τ [ ∷ θ →
          -------------------------------------------------------------------------------------
             Γ ⊢ `case t return ν of l %% r ∈ ν ⊠ θ            

    `cut : {σ : Type} {Δ : Usages γ} {t : Check n} →

              Γ ⊢ σ ∋ t ⊠ Δ →
          -----------------------
           Γ ⊢ `cut t σ ∈ σ ⊠ Δ

  data _∋_↝_ : (A : Type) {m : ℕ} (p : Pattern m) (Δ : Vec Type m) → Set where
    `v   : {σ : Type} → σ ∋ `v ↝ σ ∷ []
    _,,_ : {σ τ : Type} {m n : ℕ} {p : Pattern m} {q : Pattern n} {Δ₁ : Context m} {Δ₂ : Context n} →
          σ ∋ p ↝ Δ₁ → τ ∋ q ↝ Δ₂ → σ ⊗ τ ∋ p ,, q ↝ Δ₁ C.++ Δ₂


patternSize : {o : ℕ} {p : Pattern o} {σ : Type} {γ : Context o} (p : σ ∋ p ↝ γ) → ℕ
patternSize {o} _ = o

{-
mutual

  weak⊢∈ : {k l : ℕ} {γ : Context k} {m : Sc.Mergey k l} {M : C.Mergey m}
           {Γ Δ : Usages γ} {σ : Type} {t : Infer k}
           (𝓜 : Mergey M) → Γ ⊢ t ∈ σ ⊠ Δ → Γ ⋈ 𝓜 ⊢ weakInfer m t ∈ σ ⊠ Δ ⋈ 𝓜
  weak⊢∈ 𝓜 (`var k)                     = `var {!!}
  weak⊢∈ 𝓜 (`app t u)                   = `app (weak⊢∈ 𝓜 t) (weak⊢∋ 𝓜 u)
  weak⊢∈ 𝓜 (`case t return σ of l %% r) = `case weak⊢∈ 𝓜 t return σ of weak⊢∋ (copy 𝓜) l %% weak⊢∋ (copy 𝓜) r
  weak⊢∈ 𝓜 (`cut t)                     = `cut (weak⊢∋ 𝓜 t)

  weak⊢∋ : {k l : ℕ} {γ : Context k} {m : Sc.Mergey k l} {M : C.Mergey m}
           {Γ Δ : Usages γ} {σ : Type} {t : Check k}
           (𝓜 : Mergey M) → Γ ⊢ σ ∋ t ⊠ Δ → Γ ⋈ 𝓜 ⊢ σ ∋ weakCheck m t ⊠ Δ ⋈ 𝓜
  weak⊢∋ 𝓜 (`lam t)            = `lam weak⊢∋ (copy 𝓜) t
  weak⊢∋ {m = m} 𝓜 (`let_∷=_`in_ {σ} {τ} {o} {rp} {δ} {rt} {Δ} {θ} {ru} p t u) =
    let P    = λ {γ} (Γ Γ′ : Usages γ) → Γ ⊢ τ ∋ weakCheck (Sc.copys o m) ru ⊠ Γ′
        ih   = weak⊢∋ (copys o 𝓜) u
        cast = ++copys-elim₂ P [[ δ ]] ]] δ [[ Δ θ 𝓜
    in `let p ∷= weak⊢∈ 𝓜 t `in cast ih
  weak⊢∋ 𝓜 (`prd t u)          = {!!}
  weak⊢∋ 𝓜 (`inl t)            = {!!}
  weak⊢∋ 𝓜 (`inr t)            = {!!}
  weak⊢∋ 𝓜 (`neu t)            = {!!}
-}
