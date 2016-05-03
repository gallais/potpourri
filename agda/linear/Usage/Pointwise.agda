module linear.Usage.Pointwise where

open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_ ; cong ; subst)

open import linear.Type
open import linear.Scope as Sc hiding (copys)
open import linear.Context as C hiding (_++_ ; copys)
open import linear.Context.Pointwise as CP using (Context[_] ; [] ; _∷_)
open import linear.Usage as U hiding (_++_ ; copys)

data Usages[_,_]
  (R : (σ τ : Type) → Set)
  (𝓡 : {σ τ : Type} → R σ τ → (S : Usage σ) (T : Usage τ) → Set) :
  {k : ℕ} {γ δ : Context k} (rs : Context[ R ] γ δ) →
  (Γ : Usages γ) (Δ : Usages δ) → Set where
  
  []  : Usages[ R , 𝓡 ] [] [] []
  
  _∷_ : {σ τ : Type} {r : R σ τ} {S : Usage σ} {T : Usage τ}
        {k : ℕ} {γ δ : Context k} {rs : Context[ R ] γ δ} {Γ : Usages γ} {Δ : Usages δ} →
        𝓡 r S T → Usages[ R , 𝓡 ] rs Γ Δ →
        Usages[ R , 𝓡 ] (r ∷ rs) (S ∷ Γ) (T ∷ Δ)

_++_ : {R : (σ τ : Type) → Set} {𝓡 : {σ τ : Type} → R σ τ → Usage σ → Usage τ → Set}
       {k l : ℕ} {γ γ′ : Context k} {δ δ′ : Context l} →
       {rs : Context[ R ] γ γ′} {ss : Context[ R ] δ δ′} →
       {Γ : Usages γ} {Γ′ : Usages γ′} {Δ : Usages δ} {Δ′ : Usages δ′} →
       Usages[ R , 𝓡 ] rs Γ Γ′ → Usages[ R , 𝓡 ] ss Δ Δ′ →
       Usages[ R , 𝓡 ] (rs CP.++ ss) (Γ U.++ Δ) (Γ′ U.++ Δ′)
[]       ++ SS = SS
(R ∷ RS) ++ SS = R ∷ (RS ++ SS)


UsageEq : {σ τ : Type} → σ ≡ τ → Usage σ → Usage τ → Set
UsageEq eq rewrite eq = _≡_

refl : {k : ℕ} {γ : Context k} {Γ : Usages γ} → Usages[ _≡_ , UsageEq ] CP.refl Γ Γ
refl {Γ = []}    = []
refl {Γ = S ∷ Γ} = PEq.refl ∷ refl

sym : {k : ℕ} {γ δ : Context k} {eq : Context[ _≡_ ] γ δ} {Γ : Usages γ} {Δ : Usages δ} →
      Usages[ _≡_ , UsageEq ] eq Γ Δ → Usages[ _≡_ , UsageEq ] (CP.sym eq) Δ Γ
sym                     []         = []
sym {eq = PEq.refl ∷ _} (EQ ∷ EQs) = PEq.sym EQ ∷ sym EQs

trans :
  {k : ℕ} {γ δ θ : Context k} {eq₁ : Context[ _≡_ ] γ δ} {eq₂ : Context[ _≡_ ] δ θ} →
  {Γ : Usages γ} {Δ : Usages δ} {Θ : Usages θ} →
  Usages[ _≡_ , UsageEq ] eq₁ Γ Δ → Usages[ _≡_ , UsageEq ] eq₂ Δ Θ →
  Usages[ _≡_ , UsageEq ] (CP.trans eq₁ eq₂) Γ Θ
trans []           []           = []
trans {eq₁ = PEq.refl ∷ _} {eq₂ = PEq.refl ∷ _}
      (EQ₁ ∷ EQs₁) (EQ₂ ∷ EQs₂) = PEq.trans EQ₁ EQ₂ ∷ trans EQs₁ EQs₂

irrelevance :
  {k : ℕ} {γ δ : Context k} {eq₁ : Context[ _≡_ ] γ δ} (eq₂ : Context[ _≡_ ] γ δ)
  {Γ : Usages γ} {Δ : Usages δ} → 
  Usages[ _≡_ , UsageEq ] eq₁ Γ Δ → Usages[ _≡_ , UsageEq ] eq₂ Γ Δ
irrelevance                      []         []               = []
irrelevance {eq₁ = PEq.refl ∷ _} (PEq.refl ∷ eqs) (EQ ∷ EQs) = EQ ∷ irrelevance eqs EQs


-- coercion
coerce : {k : ℕ} {γ δ : Context k} → Context[ _≡_ ] γ δ → Usages γ → Usages δ
coerce []         []      = []
coerce (eq ∷ eqs) (S ∷ Γ) = subst Usage eq S ∷ coerce eqs Γ

coerceʳ : {k : ℕ} {γ δ : Context k} {Γ : Usages γ} (eq : Context[ _≡_ ] γ δ) →
          Usages[ _≡_ , UsageEq ] eq Γ (coerce eq Γ)
coerceʳ {Γ = []}    []              = []
coerceʳ {Γ = S ∷ Γ} (PEq.refl ∷ eq) = PEq.refl ∷ coerceʳ eq

coerceˡ : {k : ℕ} {γ δ : Context k} {Γ : Usages γ} (eq : Context[ _≡_ ] γ δ) →
            Usages[ _≡_ , UsageEq ] (CP.sym eq) (coerce eq Γ) Γ
coerceˡ {Γ = []}    []              = []
coerceˡ {Γ = S ∷ Γ} (PEq.refl ∷ eq) = PEq.refl ∷ coerceˡ eq

-- copys
copys :
  {k l o : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} {𝓜 : U.Mergey M}
  {γ : Context k} {Γ : Usages γ} {δ : Context o} (Δ : Usages δ) →
  Usages[ _≡_ , UsageEq ] (CP.copys δ) ((Δ U.++ Γ) U.⋈ U.copys o 𝓜) (Δ U.++ (Γ U.⋈ 𝓜))  
copys []      = refl
copys (T ∷ Δ) = PEq.refl ∷ (copys Δ)

pointwiseEq′ : {k : ℕ} {γ : Context k} {eq : Context[ _≡_ ] γ γ} {Γ Δ : Usages γ} →
               Usages[ _≡_ , UsageEq ] eq Γ Δ → Γ ≡ Δ
pointwiseEq′ []                                     = PEq.refl
pointwiseEq′ {eq = PEq.refl ∷ eqs} (PEq.refl ∷ EQs) = cong (_ ∷_) $ pointwiseEq′ EQs

pointwiseEq :
  {k : ℕ} {γ δ : Context k} {eq : Context[ _≡_ ] γ δ}
  {Γ : Usages γ} {Δ : Usages δ} → Usages[ _≡_ , UsageEq ] eq Γ Δ →
  subst Usages (CP.pointwiseEq eq) Γ ≡ Δ
pointwiseEq {eq = eq} EQ with CP.pointwiseEq eq
pointwiseEq EQ | PEq.refl = pointwiseEq′ EQ
