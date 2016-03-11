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

open import ptt.Context as C hiding (Context)
open import ptt.Usage
open import ptt.Type


Context = C.Context Type

infix 1 _⊢_⊠_
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

    `let_`in_ :
  
      {A B C : Type} {Δ θ : Usages γ} {a : Usage A} {b : Usage B} →
         Γ ⊢ A `⊗ B ⊠ Δ → Δ ∙ [ A ] ∙ [ B ] ⊢ C ⊠ θ ∙ a ∙ b →
      ----------------------------------------------------------- (let)
                     Γ ⊢ C ⊠ θ

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


infix 1 _⊢_
_⊢_ : (γ : Context) (A : Type) → Set
γ ⊢ A = [[ γ ]] ⊢ A ⊠ ]] γ [[

swap⊗ : ε ∙ (`ℕ `⊗ `ℝ) ⊢ `ℝ `⊗ `ℕ
swap⊗ =
  `let var z `in
  `⟨ var z , var (s z) ⟩

swap+ : ε ∙ (`ℕ `+ `ℝ) ⊢ `ℝ `+ `ℕ
swap+ =
  `case var z
  of `inr (var z)
  %% `inl (var z)
