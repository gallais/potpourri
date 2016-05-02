module linear.Typing.Substitution where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (map ; [_] ; _++_)
open import Data.Product hiding (swap)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import linear.Scope as Sc hiding (Weakening ; weakFin ; Substituting ; substFin ; copys ; Env ; withFreshVars)
open import linear.Type
open import linear.Context as C hiding (copys ; _++_)
open import linear.Language as L hiding (weakInfer ; weakCheck ; Env ; substInfer ; substCheck)
open import linear.Usage
open import linear.Usage.Functional
open import linear.Usage.Consumption hiding (_++_)
open import linear.Typing
open import linear.Typing.Functional
open import linear.Typing.Consumption

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
substFin (T ∷ ρ)  (s v) =
  let (θ , val , ρ′) = substFin ρ v
      (_ , c₁ , c₂)  = swap (consumptionInfer T) (consumptionInfer val)
  in , framingInfer c₂ val , framingInfer c₁ T ∷ ρ′
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
  {θ : Context l} {Τ₁ Τ₂ Τ₄ : Usages θ} {σ₁ σ₂ τ : Type} (t : Infer k) {l r : Check (suc k)} →
  Τ₁ ⊢ L.substInfer ρ t ∈ σ₁ ⊕ σ₂ ⊠ Τ₂ →
  Σ[ T₃ ∈ Usages (σ₁ ∷ θ) ] [ σ₁ ] ∷ Τ₂ ⊢ τ ∋ L.substCheck (v∷ ρ) l ⊠ T₃
                         × Env TInfer T₃ (v∷ ρ) (] σ₁ [ ∷ Τ₄) (] σ₁ [ ∷ Δ) →
  Σ[ T₃ ∈ Usages (σ₂ ∷ θ) ] [ σ₂ ] ∷ Τ₂ ⊢ τ ∋ L.substCheck (v∷ ρ) r ⊠ T₃
                         × Env TInfer T₃ (v∷ ρ) (] σ₂ [ ∷ Τ₄) (] σ₂ [ ∷ Δ) →
  Σ[ Τ₃ ∈ Usages θ       ] Τ₁ ⊢ L.substInfer ρ (`case t return τ of l %% r) ∈ τ ⊠ Τ₃
                         × Env TInfer Τ₃ ρ Τ₄ Δ
substCase t tρ (._ , lρ , (]v[∷ ρ₁′)) (._ , rρ , (]v[∷ ρ₂′))
  rewrite sym (functionalEnvPre functionalInferPre _ ρ₁′ ρ₂′) =
  , `case tρ return _ of lρ %% rρ , ρ₁′

-- idea: generalise with a function f applied to each side!
substLet :
  {k l o : ℕ} {γ : Context k} {Δ : Usages γ} {ρ : Sc.Env Infer k l} (δ : Context o)
  {θ : Context l} {Τ₃ : Usages θ} →
  Σ[ T₂ ∈ Usages (δ C.++ θ) ] Env TInfer T₂ (Sc.withFreshVars o ρ) (]] δ [[ ++ Τ₃) (]] δ [[ ++ Δ) →
  Σ[ Τ₂ ∈ Usages θ ] Env TInfer Τ₂ ρ Τ₃ Δ
substLet []      (Τ₂ , ρ′) = , ρ′
substLet (a ∷ δ) (._ , (]v[∷ ρ′)) = substLet δ (, ρ′)


mutual

  substInfer : Substituting Infer Infer L.substInfer TInfer TInfer
  substInfer ρ (`var x)                     = substFin ρ x
  substInfer ρ (`app t u)                   =
    let (θ₁ , tρ , ρ₁) = substInfer ρ t
        (θ₂ , uρ , ρ₂) = substCheck ρ₁ u
    in θ₂ , `app tρ uρ , ρ₂
  substInfer {t = `case rt return .σ of rl %% rr} ρ (`case t return σ of l %% r) =
    let (θ₁ , tρ , ρ₁) = substInfer ρ t
    in substCase rt tρ (substCheck ([v]∷ ρ₁) l) (substCheck ([v]∷ ρ₁) r)
  substInfer ρ (`cut t)                     =
    let (θ₁ , tρ , ρ₁) = substCheck ρ t
    in θ₁ , `cut tρ , ρ₁

  substCheck : Substituting Infer Check L.substCheck TInfer TCheck
  substCheck ρ (`lam t) = substLam (substCheck ([v]∷ ρ) t) 
  substCheck {t = `let _ ∷= rt `in ru} ρ (`let p ∷= t `in u) =
    let δ              = patternContext p
        (θ₁ , tρ , ρ₁) = substInfer ρ t
        (θ₂ , uρ , ρ₂) = substCheck (withFreshVars δ ρ₁) u
        (θ₃ , ρ)       = substLet δ (θ₂ , ρ₂)
        eq             = functionalEnvPre functionalInferPre _ ρ₂ (withStaleVars (patternContext p) ρ)
    in , `let p ∷= tρ `in subst (TCheck _ _ _) eq uρ , ρ
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
