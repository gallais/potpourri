module linear.Usage.Functional where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (_++_ ; tail ; map)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import linear.Scope as Sc hiding (Env)
open import linear.Type
open import linear.Context as C hiding (_++_)
open import linear.Usage
open import linear.Relation.Functional

R++ : {o k : ℕ} (δ : Context o) (γ : Context k) (ΔΓ : Usages (δ C.++ γ)) → (i : Usages δ) (o : Usages γ) → Set
R++ δ γ ΔΓ Δ Γ = ΔΓ ≡ (Δ ++ Γ)

functional++ : {o k : ℕ} {δ : Context o} {γ : Context k} {ΔΓ : Usages (δ C.++ γ)} → Functional′ (R++ δ γ ΔΓ)
functional++ []      refl refl = refl
functional++ (A ∷ Δ) eq₁  eq₂  = functional++ Δ (cong tail eq₁) (cong tail eq₂)

RFin : (k : Σ[ n ∈ ℕ ] Context n × Fin n) → (let (_ , γ , _) = k in Usages γ × Usages γ) → Type → Set
RFin (_ , _ , k) (Γ , Δ) σ = Γ ⊢ k ∈[ σ ]⊠ Δ

functionalFin : Functional RFin
functionalFin _ z      z      = refl
functionalFin _ (s k₁) (s k₂) = cong _ $ functionalFin _ k₁ k₂

RFinPost : (k : Σ[ n ∈ ℕ ] Σ[ γ ∈ Context n ] Usages γ × Fin n) →
           (let (_ , γ , _) = k in Type × Usages γ) → Set
RFinPost (_ , _ , Γ , k) (A , Δ) = Γ ⊢ k ∈[ A ]⊠ Δ

RFinPre : (k : Σ[ n ∈ ℕ ] Σ[ γ ∈ Context n ] Usages γ × Fin n) →
           (let (_ , γ , _) = k in Type × Usages γ) → Set
RFinPre (_ , _ , Δ , k) (A , Γ) = Γ ⊢ k ∈[ A ]⊠ Δ

functionalFinPost : Functional′ RFinPost
functionalFinPost _ z      z      = refl
functionalFinPost _ (s k₁) (s k₂) = cong (map id _) $ functionalFinPost _ k₁ k₂

functionalFinPre : Functional′ RFinPre
functionalFinPre _ z      z      = refl
functionalFinPre _ (s k₁) (s k₂) = cong _ $ functionalFinPre _ k₁ k₂

InferTypingPost :
  {T : ℕ → Set} (𝓣 : Typing T) (i : Σ[ n ∈ ℕ ] Σ[ γ ∈ Context n ] Usages γ × T n) →
  (let (_ , γ , _) = i in Type × Usages γ) → Set
InferTypingPost 𝓣 (_ , _ , Γ , t) (A , Δ) = 𝓣 Γ t A Δ

CheckTypingPost :
  {T : ℕ → Set} (𝓣 : Typing T) (i : Σ[ n ∈ ℕ ] Σ[ γ ∈ Context n ] Usages γ × Type × T n) →
  (let (_ , γ , _) = i in Usages γ) → Set
CheckTypingPost 𝓣 (_ , _ , Γ , A , t) Δ = 𝓣 Γ t A Δ

REnvPost :
  {E : ℕ → Set} (𝓔 : Typing E)
  (i : Σ[ k ∈ ℕ ] Σ[ l ∈ ℕ ] Σ[ θ ∈ Context l ] Usages θ × Sc.Env E k l × Σ[ γ ∈ Context k ] Usages γ) →
  (let (_ , l , θ , _) = i in Usages θ) → Set
REnvPost 𝓔 (_ , _ , _ , Τ₁ , ρ , _ , Γ) Τ₂ = Env 𝓔 Τ₁ ρ Τ₂ Γ

functionalEnvPost :
  {E : ℕ → Set} {𝓔 : Typing E} → Functional′ (InferTypingPost 𝓔) → Functional′ (REnvPost 𝓔)
functionalEnvPost det𝓔 _ []        []        = refl
functionalEnvPost det𝓔 _ (T₁ ∷ ρ₁) (T₂ ∷ ρ₂) rewrite cong proj₂ (det𝓔 _ T₁ T₂) = functionalEnvPost det𝓔 _ ρ₁ ρ₂
functionalEnvPost det𝓔 _ (─∷ ρ₁)   (─∷ ρ₂)   = functionalEnvPost det𝓔 _ ρ₁ ρ₂
functionalEnvPost det𝓔 _ ([v]∷ ρ₁) ([v]∷ ρ₂) = cong _ $ functionalEnvPost det𝓔 _ ρ₁ ρ₂
functionalEnvPost det𝓔 _ (]v[∷ ρ₁) (]v[∷ ρ₂) = cong _ $ functionalEnvPost det𝓔 _ ρ₁ ρ₂

InferTypingPre :
  {T : ℕ → Set} (𝓣 : Typing T) (i : Σ[ n ∈ ℕ ] Σ[ γ ∈ Context n ] Usages γ × T n) →
  (let (_ , γ , _) = i in Type × Usages γ) → Set
InferTypingPre 𝓣 (_ , _ , Δ , t) (A , Γ) = 𝓣 Γ t A Δ

CheckTypingPre :
  {T : ℕ → Set} (𝓣 : Typing T) (i : Σ[ n ∈ ℕ ] Σ[ γ ∈ Context n ] Usages γ × Type × T n) →
  (let (_ , γ , _) = i in Usages γ) → Set
CheckTypingPre 𝓣 (_ , _ , Δ , A , t) Γ = 𝓣 Γ t A Δ

REnvPre :
  {E : ℕ → Set} (𝓔 : Typing E)
  (i : Σ[ k ∈ ℕ ] Σ[ l ∈ ℕ ] Σ[ θ ∈ Context l ] Usages θ × Sc.Env E k l × Σ[ γ ∈ Context k ] Usages γ) →
  (let (_ , l , θ , _) = i in Usages θ) → Set
REnvPre 𝓔 (_ , _ , _ , Τ₂ , ρ , _ , Γ) Τ₁ = Env 𝓔 Τ₁ ρ Τ₂ Γ

functionalEnvPre :
  {E : ℕ → Set} {𝓔 : Typing E} → Functional′ (InferTypingPre 𝓔) → Functional′ (REnvPre 𝓔)
functionalEnvPre det𝓔 _ []        []        = refl
functionalEnvPre det𝓔 _ (T₁ ∷ ρ₁) (T₂ ∷ ρ₂) rewrite functionalEnvPre det𝓔 _ ρ₁ ρ₂ = cong proj₂ (det𝓔 _ T₁ T₂)
functionalEnvPre det𝓔 _ (─∷ ρ₁)   (─∷ ρ₂)   = functionalEnvPre det𝓔 _ ρ₁ ρ₂
functionalEnvPre det𝓔 _ ([v]∷ ρ₁) ([v]∷ ρ₂) = cong _ $ functionalEnvPre det𝓔 _ ρ₁ ρ₂
functionalEnvPre det𝓔 _ (]v[∷ ρ₁) (]v[∷ ρ₂) = cong _ $ functionalEnvPre det𝓔 _ ρ₁ ρ₂

InferTyping :
  {T : ℕ → Set} (𝓣 : Typing T) (ri : Σ[ n ∈ ℕ ] Σ[ γ ∈ Context n ] T n)
  (ii : let (_ , γ , _) = ri in Usages γ × Usages γ) (o : Type) → Set
InferTyping 𝓣 (_ , _ , t) (Γ , Δ) A = 𝓣 Γ t A Δ
