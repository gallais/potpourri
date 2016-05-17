module linear.Model where

open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Vec as V using ([] ; _∷_ ; toList)
open import Data.List as L using (List ; [] ; _∷_)
open import Function
open import Algebra
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality as PEq

open import linear.Scope
open import linear.Type
open import linear.Context
open import linear.Language
open import linear.Usage
open import linear.Usage.Consumption as UC
open import linear.Usage.Erasure as UE
open import linear.Typing
open import linear.Typing.Consumption

Model : Set₁
Model = List Type → Type → Set

coerce : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} (𝓜 : Model) (p q : Γ ⊆ Δ) {σ : Type} →
         𝓜 (used p) σ → 𝓜 (used q) σ
coerce 𝓜 p q {σ} = subst (flip 𝓜 σ ∘′ used) (irrelevance p q)

open Monoid (L.monoid Type)

 
record Linear (𝓜^C 𝓜^I : Model)
  : Set where
  field
    -- Infer
    var   : {σ : Type} → 𝓜^I (σ ∷ []) σ
    app   : {γ δ θ : List Type} {σ τ : Type} →
            𝓜^I γ (σ ─o τ) → 𝓜^C δ σ → γ ++ δ ≅ θ → 𝓜^I θ τ
    fst   : {γ : List Type} {σ τ : Type} → 𝓜^I γ (σ & τ) → 𝓜^I γ σ
    snd   : {γ : List Type} {σ τ : Type} → 𝓜^I γ (σ & τ) → 𝓜^I γ τ
    case  : {γ δ θ : List Type} {σ τ ν : Type} →
            𝓜^I γ (σ ⊕ τ)  → 𝓜^C (σ ∷ δ) ν → 𝓜^C (τ ∷ δ) ν → γ ++ δ ≅ θ → 𝓜^I θ ν
    cut   : {γ : List Type} {σ : Type} → 𝓜^C γ σ → 𝓜^I γ σ
    -- Check
    lam   : {γ : List Type} {σ τ : Type} → 𝓜^C (σ ∷ γ) τ → 𝓜^C γ (σ ─o τ)
    let'  : {γ δ θ : List Type} {σ τ ν : Type} →
            𝓜^I γ (σ ⊗ τ) → 𝓜^C (τ ∷ σ ∷ δ) ν → γ ++ δ ≅ θ → 𝓜^C θ ν
    prd⊗  : {γ δ θ : List Type} {σ τ : Type} →
            𝓜^C γ σ → 𝓜^C δ τ → γ ++ δ ≅ θ → 𝓜^C θ (σ ⊗ τ)
    prd&  : {γ : List Type} {σ τ : Type} → 𝓜^C γ σ → 𝓜^C γ τ → 𝓜^C γ (σ & τ)
    inl   : {γ : List Type} {σ τ : Type} → 𝓜^C γ σ → 𝓜^C γ (σ ⊕ τ)
    inr   : {γ : List Type} {σ τ : Type} → 𝓜^C γ τ → 𝓜^C γ (σ ⊕ τ)
    neu   : {γ : List Type} {σ : Type} → 𝓜^I γ σ → 𝓜^C γ σ
    -- Structural
    mix^I : {γ δ θ : List Type} {σ : Type} → 𝓜^I (γ L.++ δ) σ → γ ++ δ ≅ θ → 𝓜^I θ σ
    mix^C : {γ δ θ : List Type} {σ : Type} → 𝓜^C (γ L.++ δ) σ → γ ++ δ ≅ θ → 𝓜^C θ σ

module LINEAR {𝓜^C 𝓜^I : Model} (𝓜 : Linear 𝓜^C 𝓜^I) where

  open Linear 𝓜

  linearPattern :
    {γ δ θ : List Type} {σ ν : Type} {k : ℕ} {σp : Context k} {p : Pattern k} →
    σ ∋ p ↝ σp → 𝓜^I γ σ → 𝓜^C (toList σp L.++ δ) ν → γ ++ δ ≅ θ → 𝓜^C θ ν
  linearPattern `v t u inc = neu (app (cut (lam u)) (neu t) (UE.sym inc))
  linearPattern {δ = δ} {ν = ν} (p₁ ,, p₂) t u inc =
    let δ₁  = patternContext p₁
        δ₂  = patternContext p₂
        eq  : toList (δ₁ V.++ δ₂) L.++ δ ≡ toList δ₁ L.++ toList δ₂ L.++ δ
        eq  = let open ≡-Reasoning in
              begin
                toList (δ₁ V.++ δ₂) L.++ δ        ≡⟨ cong (L._++ δ) (toList-++ δ₁ δ₂) ⟩
                (toList δ₁ L.++ toList δ₂) L.++ δ ≡⟨ assoc (toList δ₁) (toList δ₂) δ ⟩
                toList δ₁ L.++ toList δ₂ L.++ δ
              ∎
        u'  : 𝓜^C (toList δ₁ L.++ toList δ₂ L.++ δ) ν
        u'  = subst (λ γ → 𝓜^C γ ν) eq u
        ih₁ = linearPattern p₁ var
        ih₂ = linearPattern p₂ var
        T   = app (cut (lam
                       (let' var (ih₂ (ih₁ u' (toList δ₂ ++ʳ trivial))
                                     (_ ∷ˡ trivial)) trivial)))
                  (neu t) trivial
    in mix^C (neu T) (UE.sym inc)

  LINEAR : {T : ℕ → Set} (𝓣 : Typing T) (𝓜^T : Model) → Set
  LINEAR {T} 𝓣 𝓜^T =
    {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {t : T n} {σ : Type} →
    (T : 𝓣 Γ t σ Δ) (inc : Γ ⊆ Δ) → 𝓜^T (used inc) σ

  linearFin : LINEAR TFin 𝓜^I
  linearFin z     (σ ∷ inc) rewrite used-refl inc = var
  linearFin (s k) (─∷ inc)  = linearFin k inc

  linearInfer : LINEAR TInfer 𝓜^I
  linearCheck : LINEAR TCheck 𝓜^C

  linearInfer (`var k)   inc = linearFin k inc
  linearInfer (`app f t) inc =
    let F   = linearInfer f (consumptionInfer f)
        T   = linearCheck t (consumptionCheck t)
        INC = UE.divide (consumptionInfer f) (consumptionCheck t) inc
    in app F T INC
  linearInfer (`fst t) inc = fst (linearInfer t inc)
  linearInfer (`snd t) inc = snd (linearInfer t inc)
  linearInfer (`case t return ν of l %% r) inc =
    let γ   = consumptionInfer t ; T   = linearInfer t γ
        δl  = consumptionCheck l ; L   = linearCheck l δl
        δr  = consumptionCheck r ; R   = linearCheck r δr
        δ   = UC.tail δl
        INC = UE.divide γ δ inc
    in case T (coerce 𝓜^C δl (_ ∷ δ) L) (coerce 𝓜^C δr (_ ∷ δ) R) INC
  linearInfer (`cut t) inc = cut (linearCheck t inc)

  
  linearCheck (`lam t) inc = lam (linearCheck t (_ ∷ inc))
  linearCheck (`let p ∷= t `in u) inc =
    let γ   = consumptionInfer t ; T = linearInfer t γ
        δ   = consumptionCheck u ; U = linearCheck u δ
        θ   = patternContext p
        δ′  = truncate θ δ
        INC = UE.divide γ δ′ inc
        eq  : used (pure θ UC.++ δ′) ≡ toList θ L.++ used δ′
        eq = let open ≡-Reasoning in
             begin
               used (pure θ UC.++ δ′)     ≡⟨ used-++ (pure θ) _ ⟩
               used (pure θ) L.++ used δ′ ≡⟨ cong (L._++ used δ′) (used-pure θ) ⟩
               toList θ L.++ used δ′
             ∎
        U′ : 𝓜^C (toList θ L.++ used δ′) _
        U′ = subst (λ γ → 𝓜^C γ _) eq (coerce 𝓜^C δ (pure θ UC.++ δ′) U)
    in linearPattern p T U′ INC
  linearCheck (`prd⊗ a b) inc =
    let γ   = consumptionCheck a ; A = linearCheck a γ
        δ   = consumptionCheck b ; B = linearCheck b δ
        INC = UE.divide γ δ inc
    in prd⊗ A B INC
  linearCheck (`prd& a b) inc = prd& (linearCheck a inc) (linearCheck b inc)
  linearCheck (`inl t) inc = inl (linearCheck t inc)
  linearCheck (`inr t) inc = inr (linearCheck t inc)
  linearCheck (`neu t) inc = neu (linearInfer t inc)


-- The usual formulation of Intuitionistic Linear Logic is
-- an instance of such models.

-- This presentation of ILL is taken from:
-- http://llwiki.ens-lyon.fr/mediawiki/index.php/Intuitionistic_linear_logic
-- except for the `mix` constructor allowing the user to reorganise the
-- context (on the llwiki, the context is a multiset).

infix 1 _⊢_
data _⊢_ : List Type → Type → Set where
  ax  : {σ : Type} → (σ ∷ []) ⊢ σ
  cut : {γ δ : List Type} {σ τ : Type} → γ ⊢ σ → σ ∷ δ ⊢ τ → γ L.++ δ ⊢ τ
  ⊗R  : {γ δ : List Type} {σ τ : Type} → γ ⊢ σ → δ ⊢ τ → γ L.++ δ ⊢ σ ⊗ τ
  ⊗L  : {γ : List Type} {σ τ ν : Type} → τ ∷ σ ∷ γ ⊢ ν → σ ⊗ τ ∷ γ ⊢ ν
  ─oR : {γ : List Type} {σ τ : Type} → σ ∷ γ ⊢ τ → γ ⊢ σ ─o τ
  ─oL : {γ δ : List Type} {σ τ ν : Type} → γ ⊢ σ → τ ∷ δ ⊢ ν → (σ ─o τ) ∷ γ L.++ δ ⊢ ν
  &R  : {γ : List Type} {σ τ : Type} → γ ⊢ σ → γ ⊢ τ → γ ⊢ σ & τ
  &₁L : {γ : List Type} {σ τ ν : Type} → σ ∷ γ ⊢ ν  → σ & τ ∷ γ ⊢ ν
  &₂L : {γ : List Type} {σ τ ν : Type} → τ ∷ γ ⊢ ν  → σ & τ ∷ γ ⊢ ν
  ⊕₁R : {γ : List Type} {σ τ : Type} → γ ⊢ σ → γ ⊢ σ ⊕ τ
  ⊕₂R : {γ : List Type} {σ τ : Type} → γ ⊢ τ → γ ⊢ σ ⊕ τ
  ⊕L  : {γ : List Type} {σ τ ν : Type} → σ ∷ γ ⊢ ν → τ ∷ γ ⊢ ν → σ ⊕ τ ∷ γ ⊢ ν
  mix : {γ δ θ : List Type} {σ : Type} → γ L.++ δ ⊢ σ → γ ++ δ ≅ θ → θ ⊢ σ


ILL : Linear _⊢_ _⊢_
ILL = record
  { var   = ax
  ; app   = λ f t inc →
            let F = cut f (─oL t ax)
            in mix F (subst (_ ++_≅ _) (PEq.sym $ proj₂ identity _) inc)
  ; fst   = λ t → subst (_⊢ _) (proj₂ identity _) (cut t (&₁L ax))
  ; snd   = λ t → subst (_⊢ _) (proj₂ identity _) (cut t (&₂L ax))
  ; case  = λ t l r → mix (cut t (⊕L l r))
  ; cut   = id
  ; lam   = ─oR
  ; let'  = λ t u → mix (cut t (⊗L u))
  ; prd⊗  = λ a b → mix (⊗R a b)
  ; prd&  = &R
  ; inl   = ⊕₁R
  ; inr   = ⊕₂R
  ; neu   = id
  ; mix^I = mix
  ; mix^C = mix
  }

-- Immediate consequence: every derivation in our extension
-- gives rise to a derivation in ILL

illCheck : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {t : Check n} {σ : Type} →
           Γ ⊢ σ ∋ t ⊠ Δ → ∃ λ γ → γ ⊢ σ
illCheck T = , LINEAR.linearCheck ILL T (consumptionCheck T)

illInfer : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {t : Infer n} {σ : Type} →
           Γ ⊢ t ∈ σ ⊠ Δ → ∃ λ γ → γ ⊢ σ
illInfer T = , LINEAR.linearInfer ILL T (consumptionInfer T)
