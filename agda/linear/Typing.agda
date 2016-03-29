module linear.Typing where

open import Data.Nat as ℕ
open import Data.Fin
open import Data.Vec hiding ([_] ; _++_)

open import linear.Type
open import linear.Scope as Sc hiding (Mergey ; copys ; Weakening ; Substituting)
open import linear.Context as C hiding (Mergey ; _⋈_ ; copys ; _++_ ; ++copys-elim)
open import linear.Language hiding (patternSize)
open import linear.Usage

infix 3 _⊢_∋_⊠_ _⊢_∈_⊠_ _∋_↝_
mutual
  
  data _⊢_∋_⊠_ {n : ℕ} {γ : Context n} (Γ : Usages γ) : (A : Type) (t : Check n) (Δ : Usages γ) → Set where

    `lam_ : {σ τ : Type} {b : Check (suc n)} {Δ : Usages γ} →
    
             [ σ ] ∷ Γ ⊢ τ ∋ b ⊠ ] σ [ ∷ Δ →
           -------------------------
            Γ ⊢ σ ─o τ ∋ `lam b ⊠ Δ

    `let_∷=_`in_ : {σ τ : Type} {o : ℕ} {p : Pattern o} {δ : Context o} {t : Infer n}
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
    
  data _⊢_∈_⊠_ {n : ℕ} {γ : Context n} (Γ : Usages γ) : (t : Infer n) (A : Type) (Δ : Usages γ) → Set where

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

  data _∋_↝_ : (A : Type) {m : ℕ} (p : Pattern m) (Δ : Context m) → Set where
    `v   : {σ : Type} → σ ∋ `v ↝ σ ∷ []
    _,,_ : {σ τ : Type} {m n : ℕ} {p : Pattern m} {q : Pattern n} {Δ₁ : Context m} {Δ₂ : Context n} →
          σ ∋ p ↝ Δ₁ → τ ∋ q ↝ Δ₂ → σ ⊗ τ ∋ p ,, q ↝ Δ₁ C.++ Δ₂

-- dirty hack
patternSize : {o : ℕ} {p : Pattern o} {σ : Type} {γ : Context o} (p : σ ∋ p ↝ γ) → ℕ
patternSize {o} _ = o

-- We can give an abstract interface to describe these relations
-- by introducing the notion of `Typing`. It exists for `Fin`,
-- `Check` and `Infer`:

Typing : (T : ℕ → Set) → Set₁
Typing T = {n : ℕ} {γ : Context n} (Γ : Usages γ) (t : T n) (A : Type) (Δ : Usages γ) → Set

TFin : Typing Fin
TFin = _⊢_∈[_]⊠_

TCheck : Typing Check
TCheck = λ Γ t A Δ → Γ ⊢ A ∋ t ⊠ Δ

TInfer : Typing Infer
TInfer = _⊢_∈_⊠_

-- The notion of 'Usage Weakening' can be expressed for `Typing`s of
-- `T` if it enjoys `Scope Weakening`.

Weakening : (T : ℕ → Set) (Wk : Sc.Weakening T) (𝓣 : Typing T) → Set
Weakening T Wk 𝓣 =
  {k l : ℕ} {γ : Context k} {Γ Δ : Usages γ} {m : Sc.Mergey k l} {M : C.Mergey m} {σ : Type}
  {t : T k} (𝓜 : Mergey M) → 𝓣 Γ t σ Δ → 𝓣 (Γ ⋈ 𝓜) (Wk m t) σ (Δ ⋈ 𝓜)

weakVar : Weakening Fin weakFin TFin
weakVar finish        k    = k
weakVar (insert A 𝓜) k     = s (weakVar 𝓜 k)
weakVar (copy 𝓜)     z     = z
weakVar (copy 𝓜)     (s k) = s (weakVar 𝓜 k)

mutual

  weak⊢∈ : Weakening Infer weakInfer TInfer
  weak⊢∈ 𝓜 (`var k)                     = `var (weakVar 𝓜 k)
  weak⊢∈ 𝓜 (`app t u)                   = `app (weak⊢∈ 𝓜 t) (weak⊢∋ 𝓜 u)
  weak⊢∈ 𝓜 (`case t return σ of l %% r) = `case weak⊢∈ 𝓜 t return σ of weak⊢∋ (copy 𝓜) l %% weak⊢∋ (copy 𝓜) r
  weak⊢∈ 𝓜 (`cut t)                     = `cut (weak⊢∋ 𝓜 t)

  weak⊢∋ : Weakening Check weakCheck TCheck
  weak⊢∋ 𝓜 (`lam t)            = `lam weak⊢∋ (copy 𝓜) t
  weak⊢∋ {m = m} 𝓜 (`let_∷=_`in_ {σ} {τ} {o} {rp} {δ} {rt} {Δ} {θ} {ru} p t u) =
    let P    = λ {γ} (Γ Γ′ : Usages γ) → Γ ⊢ τ ∋ weakCheck (Sc.copys o m) ru ⊠ Γ′
        ih   = weak⊢∋ (copys o 𝓜) u
        cast = ++copys-elim₂ P [[ δ ]] ]] δ [[ Δ θ 𝓜
    in `let p ∷= weak⊢∈ 𝓜 t `in cast ih
  weak⊢∋ 𝓜 (`prd t u)          = `prd (weak⊢∋ 𝓜 t) (weak⊢∋ 𝓜 u)
  weak⊢∋ 𝓜 (`inl t)            = `inl weak⊢∋ 𝓜 t
  weak⊢∋ 𝓜 (`inr t)            = `inr weak⊢∋ 𝓜 t
  weak⊢∋ 𝓜 (`neu t)            = `neu weak⊢∈ 𝓜 t
