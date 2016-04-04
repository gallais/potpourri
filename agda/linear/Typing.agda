module linear.Typing where

open import Data.Nat as ℕ
open import Data.Fin
open import Data.Product
open import Data.Vec hiding ([_] ; _++_ ; map)
open import Function

open import linear.Type
open import linear.Scope as Sc
  hiding (Mergey ; copys ; Weakening ; weakFin ; Substituting ; substFin ; Env ; Freshey ; withFreshVars)
open import linear.Context as C hiding (Mergey ; _⋈_ ; copys ; _++_ ; ++copys-elim)
open import linear.Language as L
  hiding (patternSize ; weakInfer ; weakCheck ; substInfer ; substCheck ; Env
         ; fresheyInfer)
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

patternContext : {o : ℕ} {p : Pattern o} {σ : Type} {γ : Context o} (p : σ ∋ p ↝ γ) → Context o
patternContext {γ = γ} _ = γ

TCheck : Typing Check
TCheck = λ Γ t A Δ → Γ ⊢ A ∋ t ⊠ Δ

TInfer : Typing Infer
TInfer = _⊢_∈_⊠_

mutual

  weakInfer : Weakening Infer L.weakInfer TInfer
  weakInfer 𝓜 (`var k)                     = `var (weakFin 𝓜 k)
  weakInfer 𝓜 (`app t u)                   = `app (weakInfer 𝓜 t) (weakCheck 𝓜 u)
  weakInfer 𝓜 (`case t return σ of l %% r) = `case weakInfer 𝓜 t return σ
                                                of weakCheck (copy 𝓜) l
                                                %% weakCheck (copy 𝓜) r
  weakInfer 𝓜 (`cut t)                     = `cut (weakCheck 𝓜 t)

  weakCheck : Weakening Check L.weakCheck TCheck
  weakCheck 𝓜 (`lam t)            = `lam weakCheck (copy 𝓜) t
  weakCheck {m = m} 𝓜 (`let_∷=_`in_ {σ} {τ} {o} {rp} {δ} {rt} {Δ} {θ} {ru} p t u) =
    let P    = λ {γ} (Γ Γ′ : Usages γ) → Γ ⊢ τ ∋ L.weakCheck (Sc.copys o m) ru ⊠ Γ′
        ih   = weakCheck (copys o 𝓜) u
        cast = ++copys-elim₂ P [[ δ ]] ]] δ [[ Δ θ 𝓜
    in `let p ∷= weakInfer 𝓜 t `in cast ih
  weakCheck 𝓜 (`prd t u)          = `prd (weakCheck 𝓜 t) (weakCheck 𝓜 u)
  weakCheck 𝓜 (`inl t)            = `inl weakCheck 𝓜 t
  weakCheck 𝓜 (`inr t)            = `inr weakCheck 𝓜 t
  weakCheck 𝓜 (`neu t)            = `neu weakInfer 𝓜 t

substFin : 
  {k l : ℕ} {γ : Context k} {Γ Δ : Usages γ} {σ : Type} {v : Fin k} {ρ : Sc.Env Infer k l}
  {θ : Context l} {Τ₁ Τ₂ : Usages θ} →
  Env TInfer Τ₁ ρ Τ₂ Γ → Γ ⊢ v ∈[ σ ]⊠ Δ →
  ∃ λ Τ₃ → Τ₁ ⊢ Sc.substFin L.fresheyInfer ρ v ∈ σ ⊠ Τ₃ × Env TInfer Τ₃ ρ Τ₂ Δ
substFin (t ∷ ρ)  z     = , t , ─∷ ρ
substFin ([v]∷ ρ) z     = , `var z , ]v[∷ ρ
substFin (T ∷ ρ)  (s v) = map {!!} (map {!!} {!T ∷_!}) $ substFin ρ v -- argh!
substFin ([v]∷ ρ) (s v) = map ([ _ ] ∷_) (map (weakInfer (insert _ finish)) [v]∷_) $ substFin ρ v
substFin (]v[∷ ρ) (s v) = map (] _ [ ∷_) (map (weakInfer (insert _ finish)) ]v[∷_) $ substFin ρ v
substFin (─∷ ρ)   (s v) = map id (map id ─∷_) $ substFin ρ v

substLam :
  {k l : ℕ} {γ : Context k} {Δ : Usages γ} {ρ : Sc.Env Infer k l}
  {θ : Context l} {Τ₁ Τ₂ : Usages θ} {σ τ : Type} {b : Check (suc k)} →
  Σ[ T₃ ∈ Usages (σ ∷ θ) ] [ σ ] ∷ Τ₁ ⊢ τ ∋ L.substCheck (v∷ ρ) b ⊠ T₃
                         × Env TInfer T₃ (v∷ ρ) (] σ [ ∷ Τ₂) (] σ [ ∷ Δ) →
  Σ[ Τ₃ ∈ Usages θ       ] Τ₁ ⊢ σ ─o τ ∋ L.substCheck ρ (`lam b) ⊠ Τ₃
                         × Env TInfer Τ₃ ρ Τ₂ Δ
substLam (._ , bρ , ]v[∷ ρ′) = , `lam bρ , ρ′

substCase :
  {k l : ℕ} {γ : Context k} {Δ : Usages γ} {ρ : Sc.Env Infer k l}
  {θ : Context l} {Τ₁ Τ₂ Τ₄ : Usages θ} {σ₁ σ₂ τ : Type} {t : Infer k} {l r : Check (suc k)} →
  Τ₁ ⊢ L.substInfer ρ t ∈ σ₁ ⊕ σ₂ ⊠ Τ₂ →
  Σ[ T₃ ∈ Usages (σ₁ ∷ θ) ] [ σ₁ ] ∷ Τ₂ ⊢ τ ∋ L.substCheck (v∷ ρ) l ⊠ T₃
                         × Env TInfer T₃ (v∷ ρ) (] σ₁ [ ∷ Τ₄) (] σ₁ [ ∷ Δ) →
  Σ[ T₃ ∈ Usages (σ₂ ∷ θ) ] [ σ₂ ] ∷ Τ₂ ⊢ τ ∋ L.substCheck (v∷ ρ) r ⊠ T₃
                         × Env TInfer T₃ (v∷ ρ) (] σ₂ [ ∷ Τ₄) (] σ₂ [ ∷ Δ) →
  Σ[ Τ₃ ∈ Usages θ       ] Τ₁ ⊢ L.substInfer ρ (`case t return τ of l %% r) ∈ τ ⊠ Τ₃
                         × Env TInfer Τ₃ ρ Τ₄ Δ
substCase tρ (._ , lρ , (]v[∷ ρ′)) (._ , rρ , (]v[∷ ρ₂′)) =
  , `case tρ return _ of lρ %% {!rρ!} , ρ′


mutual

  substInfer : Substituting Infer Infer L.substInfer TInfer TInfer
  substInfer ρ (`var x)                     = substFin ρ x
  substInfer ρ (`app t u)                   =
    let (θ₁ , tρ , ρ₁) = substInfer ρ t
        (θ₂ , uρ , ρ₂) = substCheck ρ₁ u
    in θ₂ , `app tρ uρ , ρ₂
  substInfer ρ (`case t return σ of l %% r) =
    let (θ₁ , tρ , ρ₁) = substInfer ρ t
    in substCase tρ (substCheck ([v]∷ ρ₁) l) (substCheck ([v]∷ ρ₁) r)
  substInfer ρ (`cut t)                     =
    let (θ₁ , tρ , ρ₁) = substCheck ρ t
    in θ₁ , `cut tρ , ρ₁

  substCheck : Substituting Infer Check L.substCheck TInfer TCheck
  substCheck ρ (`lam t) = substLam (substCheck ([v]∷ ρ) t) 
  substCheck ρ (`let p ∷= t `in u) =
    let (θ₁ , tρ , ρ₁) = substInfer ρ t
        (θ₂ , uρ , ρ₂) = substCheck (withFreshVars (patternContext p) ρ₁) u
    in {!!}
  substCheck ρ (`prd a b) =
    let (θ₁ , aρ , ρ₁) = substCheck ρ a
        (θ₂ , bρ , ρ₂) = substCheck ρ₁ b
    in θ₂ , `prd aρ bρ , ρ₂
  substCheck ρ (`inl t) =
    let (θ₁ , tρ , ρ₁) = substCheck ρ t
    in θ₁ , `inl tρ , ρ₁
  substCheck ρ (`inr t) =
    let (θ₁ , tρ , ρ₁) = substCheck ρ t
    in θ₁ , `inr tρ , ρ₁
  substCheck ρ (`neu t) =
    let (θ₁ , tρ , ρ₁) = substInfer ρ t
    in θ₁ , `neu tρ , ρ₁

