-- This alternative presentation of the language is mainly motivated
-- by the fact that too many essentially-equal terms where given a
-- different representation in ptt.Language:

--   Γ ⊢ 1    Δ ⊢ 1                          Γ ++ Δ ⊢ 1    ε ⊢ 1
-- ------------------  was different from  ----------------------
--   Γ ++ Δ ⊢ 1 ⊗ 1                           Γ ++ Δ ⊢ 1 ⊗ 1
--
--           Δ ⊢ 1    Γ ⊢ 1
-- or even  ------------------
--            Γ ++ Δ ⊢ 1 ⊗ 1
--
-- Indeed, the type system being affine means that resources which
-- aren't used may be discarded. And we get the opportunity to do
-- so at all the leaves in the derivation tree which guarantees the
-- validity of a more general "weakening" lemma on whole derivations).
-- But this approach is fundamentally flawed: the only important fact
-- about discarded resources is that they are discarded, not where it
-- happens.

-- A resource-centric presentation of the system similar to the work
-- Conor and I did on Intuitionistic Linear Logic with Leftovers should
-- do the trick: http://gallais.github.io/proof-search-ILLWiL/

module ptt.ConsumptionLanguage where

open import ptt.Context as C hiding (Context ; Holey)
open import ptt.Usage
open import ptt.Type
open import Data.Nat

Context = C.Context Type
Holey   = C.Holey   Type

infix 1 _⊢_⊠_

infixr 10 _,_
data Pattern : (A : Type) → Holey → Set where
  _,_ : {A B : Type} {Γ Δ : Holey} → Pattern A Γ → Pattern B Δ → Pattern (A `⊗ B) (Γ ∘ Δ)
  `v  : {A : Type} → Pattern A ([] ∙ A) -- a variable we are going to use
  `─  : {A : Type} → Pattern A []       -- one we'll do away with

pre : {A : Type} {h : Holey} {γ : Context} (p : Pattern A h) → Usages γ → Usages (h ⇐ γ)
pre     (p , q) Γ = pre p (pre q Γ)
pre {A} `v      Γ = Γ ∙ [ A ]
pre {A} `─      Γ = Γ

post : {A : Type} {h : Holey} {γ : Context} (p : Pattern A h) → Usages γ → Usages (h ⇐ γ)
post     (p , q) Γ = post p (post q Γ)
post {A} `v      Γ = Γ ∙ ] A [
post {A} `─      Γ = Γ

data _⊢_⊠_ {γ : Context} (Γ : Usages γ) : (A : Type) (Δ : Usages γ) → Set where

  -- VARIABLE
    var :
      {Δ : Usages γ} {A : Type} →
            Γ ∋ A ⊠ Δ →
      --------------------- (var)
            Γ ⊢ A ⊠ Δ

  -- ZERO

    `¡ :
      {Δ : Usages γ} {A : Type} →
           Γ ⊢ `0 ⊠ Δ → 
     ----------------------- (magic)
           Γ ⊢ A ⊠ Δ

  -- UNIT
    `*  :
      -------------- (unit)
        Γ ⊢ `1 ⊠ Γ

  -- TENSOR
    `⟨_,_⟩ :
  
      {A B : Type} {Δ θ : Usages γ} →
        Γ ⊢ A ⊠ Δ → Δ ⊢ B ⊠ θ →
      ------------------------- (⊗)
            Γ ⊢ A `⊗ B ⊠ θ

    `let_∷=_`in_ :
  
      {A B : Type} {h : Holey} {Δ θ : Usages γ} →
         (p : Pattern A h) → Γ ⊢ A ⊠ Δ → pre p Δ ⊢ B ⊠ post p θ →
      ----------------------------------------------------------- (let)
                     Γ ⊢ B ⊠ θ

  -- SUM
    `inl :
      {Δ : Usages γ} {A B : Type} →
            Γ ⊢ A ⊠ Δ →
      --------------------- (inl)
          Γ ⊢ A `+ B ⊠ Δ

    `inr :
      {Δ : Usages γ} {A B : Type} →
            Γ ⊢ B ⊠ Δ →
      --------------------- (inl)
          Γ ⊢ A `+ B ⊠ Δ

    `case_of_%%_ :
      {A B C : Type} {Δ θ : Usages γ} {a : Usage A} {b : Usage B} →
        Γ ⊢ A `+ B ⊠ Δ → Δ ∙ [ A ] ⊢ C ⊠ θ ∙ a → Δ ∙ [ B ] ⊢ C ⊠ θ ∙ b → 
      ----------------------------------------------------------------- (case)
                            Γ ⊢ C ⊠ θ

  -- INSTRUMENT

    `instr :
      {A : Type} {a : Usages (ε ∙ A)} {Δ : Usages γ}
          (n : ℕ) → ε ∙ [ A ] ⊢ `[ n ] ⊠ a → Γ ⊢ A ⊠ Δ →
      --------------------------------------------------- (instr)
                 Γ ⊢ `[ n ]∙ A ⊠ Δ

  -- RATIO

    `1/_ :
          (n : ℕ) →
       --------------- (1/2+n)
         Γ ⊢ `2 ⊠ Γ


infix 1 _⊢_
_⊢_ : (γ : Context) (A : Type) → Set
γ ⊢ A = [[ γ ]] ⊢ A ⊠ ]] γ [[

fst⊗ : {A B : Type} → ε ∙ (A `⊗ B) ⊢ A
fst⊗ =
  `let (`v , `─) ∷= var z
  `in var z

swap⊗ : ε ∙ (`ℕ `⊗ `ℝ) ⊢ `ℝ `⊗ `ℕ
swap⊗ =
  `let (`v , `v) ∷= var z `in
  `⟨ var (s z) , var z ⟩

rotate₅ : {A B C D E : Type} → ε ∙ (A `⊗ B `⊗ C `⊗ D `⊗ E) ⊢ B `⊗ C `⊗ D `⊗ E `⊗ A
rotate₅ =
  `let (`v , `v , `v , `v , `v) ∷= var z `in
  `⟨ var (s z) , `⟨ var (s (s z)) , `⟨ var (s (s (s z))) , `⟨ var (s (s (s (s z)))) , var z ⟩ ⟩ ⟩ ⟩

middle⊗₁ : {A B C : Type} → ε ∙ ((A `⊗ B) `⊗ C) ⊢ B
middle⊗₁ =
  `let (`v , `─) ∷= var z `in
  `let (`─ , `v) ∷= var z `in var z
  
middle⊗₂ : {A B C : Type} → ε ∙ ((A `⊗ B) `⊗ C) ⊢ B
middle⊗₂ = `let ((`─ , `v) , `─) ∷= var z `in var z

swap+ : ε ∙ (`ℕ `+ `ℝ) ⊢ `ℝ `+ `ℕ
swap+ =
  `case var z
  of `inr (var z)
  %% `inl (var z)
