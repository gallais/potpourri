module linear.Typecheck where

open import Function
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _++_ ; tail)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import linear.Type as Type
open import linear.Context as C hiding (_++_)
open import linear.Usage
open import linear.Usage.Equality as UsageEq
open import linear.Language
open import linear.Typing
open import linear.Typing.Inversion
open import linear.Typing.Functional
open import linear.RawIso
open import linear.Typecheck.Problem

-- Decidability of Type-checking

consume : {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) → Dec $ CONSUME Γ k
consume ([ σ ] ∷ Γ) zero    = yes (σ , ] σ [ ∷ Γ , z)
consume (] σ [ ∷ Γ) zero    = no (λ { (_ , _ , ()) })
consume (σ ∷ Γ)     (suc k) = consumeSuc Γ σ k <$> consume Γ k

checkPattern : {n : ℕ} (σ : Type) (p : Pattern n) → Dec $ PATTERN σ p
checkPattern σ `v              = yes (σ ∷ [] , `v)
checkPattern (σ ⊗ τ)  (p ,, q) = patternTensor <$> checkPattern σ p <*> checkPattern τ q
checkPattern (κ x)    (p ,, q) = no (λ { (_ , ()) })
checkPattern (σ ⊕ τ)  (p ,, q) = no (λ { (_ , ()) })
checkPattern (σ ─o τ) (p ,, q) = no (λ { (_ , ()) })

truncate : {n o : ℕ} {γ : Context n} (δ : Context o) (Γ : Usages (δ C.++ γ)) → Dec $ TRUNCATE δ Γ
truncate []      Γ            = yes (Γ , refl)
truncate (a ∷ δ) ([ .a ] ∷ Γ) = no (λ { (_ , ()) })
truncate (a ∷ δ) (] .a [ ∷ Γ) = truncateUsed δ Γ <$> truncate δ Γ

mutual

  infer : {n : ℕ} {γ : Context n} (Γ : Usages γ) (t : Infer n) → Dec $ INFER Γ t

  -- VAR
  infer Γ (`var k)                     = inferVar Γ k <$> consume Γ k

  -- APP
  infer Γ (`app t u)
    with infer Γ t
  ... | no ¬p = no $ λ p → ¬p (_ , _ , app-inv-function (INFER.proof p))
  ... | yes (σ ⊗ τ , _ , T) = no $ λ p → case functionalInfer _ T (app-inv-function $ INFER.proof p) of λ ()
  ... | yes (σ ⊕ τ , _ , T) = no $ λ p → case functionalInfer _ T (app-inv-function $ INFER.proof p) of λ ()
  ... | yes (κ n   , _ , T) = no $ λ p → case functionalInfer _ T (app-inv-function $ INFER.proof p) of λ ()
  ... | yes (σ ─o τ , Δ , T)
    with check Δ σ u
  ... | no ¬p = no $ λ p → let eq     = functionalInferPost _ (app-inv-function (INFER.proof p)) T
                               coerce = subst₂ (_⊢_∋ _ ⊠ _) (cong proj₂ eq) (proj₁ $ ─o-inj $ cong proj₁ eq)
                           in ¬p (_ , coerce (app-inv-argument (INFER.proof p)))
  ... | yes (θ , U) = yes (τ , θ , `app T U)

  -- CASE
  infer Γ (`case t return ν of l %% r)
    with infer Γ t
  ... | no ¬p = no $ λ p → ¬p (_ , _ , case-inv-scrutinee (INFER.proof p))
  ... | yes (σ ⊗ τ  , _ , T) = no $ λ p → case functionalInfer _ T (case-inv-scrutinee $ INFER.proof p) of λ ()
  ... | yes (σ ─o τ , _ , T) = no $ λ p → case functionalInfer _ T (case-inv-scrutinee $ INFER.proof p) of λ ()
  ... | yes (κ n    , _ , T) = no $ λ p → case functionalInfer _ T (case-inv-scrutinee $ INFER.proof p) of λ ()
  ... | yes (σ ⊕ τ  , Δ , T)
    with check ([ σ ] ∷ Δ) ν l | check ([ τ ] ∷ Δ) ν r
  ... | no ¬l | _     = no $ λ p →
    let eq     = functionalInferPost _ (case-inv-scrutinee $ INFER.proof p) T
        coerce = subst₂ (λ Δ σ → [ σ ] ∷ Δ ⊢ ν ∋ l ⊠ ] σ [ ∷ _) (cong proj₂ eq) (proj₁ $ ⊕-inj $ cong proj₁ eq)
    in ¬l (_ , coerce (case-inv-left (INFER.proof p)))
  ... | _     | no ¬r = no $ λ p →
    let eq     = functionalInferPost _ (case-inv-scrutinee $ INFER.proof p) T
        coerce = subst₂ (λ Δ τ → [ τ ] ∷ Δ ⊢ ν ∋ r ⊠ ] τ [ ∷ _) (cong proj₂ eq) (proj₂ $ ⊕-inj $ cong proj₁ eq)
    in ¬r (_ , coerce (case-inv-right (INFER.proof p)))
  ... | yes ([ .σ ] ∷ θ₁ , L) | _ = no $ λ p →
    let eq     = functionalInferPost _ (case-inv-scrutinee (INFER.proof p)) T
        coerce = subst₂ (λ σ θ → [ σ ] ∷ θ ⊢ ν ∋ l ⊠ ] σ [ ∷ _) (proj₁ $ ⊕-inj $ cong proj₁ eq) (cong proj₂ eq)
    in case functionalCheckPost _ (coerce (case-inv-left (INFER.proof p))) L of λ ()
  ... | _ | yes ([ .τ ] ∷ θ₂ , R) = no $ λ p →
    let eq     = functionalInferPost _ (case-inv-scrutinee (INFER.proof p)) T
        coerce = subst₂ (λ σ θ → [ σ ] ∷ θ ⊢ ν ∋ r ⊠ ] σ [ ∷ _) (proj₂ $ ⊕-inj $ cong proj₁ eq) (cong proj₂ eq)
    in case functionalCheckPost _ (coerce (case-inv-right (INFER.proof p))) R of λ ()
  ... | yes (] .σ [ ∷ θ₁ , L) | yes (] .τ [ ∷ θ₂ , R)
    with eqs θ₁ θ₂
  ... | no ¬eq = no $ λ p →
    let eq      = functionalInferPost _ (case-inv-scrutinee (INFER.proof p)) T
        coerceˡ = subst₂ (λ σ θ → [ σ ] ∷ θ ⊢ ν ∋ l ⊠ ] σ [ ∷ _) (proj₁ $ ⊕-inj $ cong proj₁ eq) (cong proj₂ eq)
        coerceʳ = subst₂ (λ σ θ → [ σ ] ∷ θ ⊢ ν ∋ r ⊠ ] σ [ ∷ _) (proj₂ $ ⊕-inj $ cong proj₁ eq) (cong proj₂ eq)
        eq₁     = functionalCheckPost _ (coerceˡ (case-inv-left (INFER.proof p))) L
        eq₂     = functionalCheckPost _ (coerceʳ (case-inv-right (INFER.proof p))) R
    in ¬eq $ trans (sym $ cong tail eq₁) (cong tail eq₂)
  ... | yes eq rewrite eq = yes (ν , _ , `case T return ν of L %% R)

  -- CUT
  infer Γ (`cut t σ)                   = inferCut Γ t σ <$> check Γ σ t

  check : {n : ℕ} {γ : Context n} (Γ : Usages γ) (σ : Type) (t : Check n) → Dec $ CHECK Γ σ t

  -- NEU
  check Γ σ (`neu t)
    with infer Γ t
  ... | no ¬p = no $ λ p → case ¬p (_ , _ , (neu-inv $ CHECK.proof p)) of λ ()
  ... | yes (τ , Δ , p)
    with Type.eq σ τ
  ... | no ¬σ≡τ = no $ λ q → ¬σ≡τ $ functionalInfer _ (neu-inv $ CHECK.proof q) p
  check Γ σ (`neu t) | yes (.σ , Δ , p) | yes refl = yes (Δ , `neu p)

  check Γ σ (`let p ∷= t `in u)
    with infer Γ t
  ... | no ¬p = no $ λ p → ¬p (_ , _ , let-inv-bound (CHECK.proof p))
  ... | yes (τ , Δ , T)
    with checkPattern τ p
  ... | no ¬p = no $ λ p → let eq     = functionalInfer _ (let-inv-bound (CHECK.proof p)) T
                               coerce = subst (_∋ _ ↝ (patternContext (let-inv-pattern (CHECK.proof p)))) eq
                           in ¬p (_ , (coerce (let-inv-pattern (CHECK.proof p))))
  ... | yes (δ , P)
    with check ([[ δ ]] ++ Δ) σ u
  ... | no ¬q = no $ λ q →
    let eq₁     = functionalInferPost _ (let-inv-bound (CHECK.proof q)) T
        coerce₁ = subst (_∋ p ↝ patternContext (let-inv-pattern (CHECK.proof q))) (cong proj₁ eq₁)
        eq₂     = functionalPattern _ (coerce₁ (let-inv-pattern (CHECK.proof q))) P
        coerce₂ = subst₂ (λ δ Δ → [[ δ ]] ++ Δ ⊢ σ ∋ u ⊠ ]] δ [[ ++ _) eq₂ (cong proj₂ eq₁) 
    in ¬q (_ , coerce₂ (let-inv-body (CHECK.proof q)))
  ... | yes (θ , U)
    with truncate δ θ
  ... | no ¬q = no $ λ q →
    let eq₁     = functionalInferPost _ (let-inv-bound (CHECK.proof q)) T
        coerce₁ = subst (_∋ p ↝ patternContext (let-inv-pattern (CHECK.proof q))) (cong proj₁ eq₁)
        eq₂     = functionalPattern _ (coerce₁ (let-inv-pattern (CHECK.proof q))) P
        coerce₂ = subst₂ (λ δ Δ → [[ δ ]] ++ Δ ⊢ σ ∋ u ⊠ ]] δ [[ ++ _) eq₂ (cong proj₂ eq₁)
        eq₃     = functionalCheckPost _ (coerce₂ (let-inv-body (CHECK.proof q))) U
    in ¬q (_ , sym eq₃)
  ... | yes (ξ , eq) rewrite eq = yes (_ , `let P ∷= T `in U)

  -- LAM
  check Γ (σ ─o τ) (`lam b)
    with check ([ σ ] ∷ Γ) τ b
  ... | no ¬p                = no $ λ p → ¬p (_ , lam-inv (CHECK.proof p))
  ... | yes ([ .σ ] ∷ Δ , p) = no λ q → case functionalCheckPost _ p (lam-inv $ CHECK.proof q) of λ ()
  ... | yes (] .σ [ ∷ Δ , p) = yes (Δ , `lam p)
  check Γ (σ ⊕ τ) (`lam b) = no $ λ p → case CHECK.proof p of λ ()
  check Γ (σ ⊗ τ) (`lam b) = no $ λ p → case CHECK.proof p of λ ()
  check Γ (κ n)   (`lam b) = no $ λ p → case CHECK.proof p of λ ()

  -- PRD
  check Γ (σ ⊗ τ)  (`prd t u)
    with check Γ σ t
  ... | no ¬p = no $ λ p → ¬p (_ , prd-inv-fst (CHECK.proof p))
  ... | yes (θ , T)
    with check θ τ u
  ... | no ¬p = no $ λ p → let eq     = functionalCheckPost _ (prd-inv-fst (CHECK.proof p)) T
                               coerce = subst (_⊢ τ ∋ u ⊠ _) eq
                           in ¬p (_ , coerce (prd-inv-snd (CHECK.proof p)))
  ... | yes (Δ , U) = yes (Δ , `prd T U)
  check Γ (σ ⊕ τ)  (`prd t u) = no $ λ p → case CHECK.proof p of λ ()
  check Γ (σ ─o τ) (`prd t u) = no $ λ p → case CHECK.proof p of λ ()
  check Γ (κ n)    (`prd t u) = no $ λ p → case CHECK.proof p of λ ()

  -- INL
  check Γ (σ ⊕ τ)  (`inl t) = checkInl Γ t σ τ <$> check Γ σ t
  check Γ (σ ⊗ τ)  (`inl t) = no $ λ p → case CHECK.proof p of λ ()
  check Γ (σ ─o τ) (`inl t) = no $ λ p → case CHECK.proof p of λ ()
  check Γ (κ n)    (`inl t) = no $ λ p → case CHECK.proof p of λ ()

  -- INR
  check Γ (σ ⊕ τ)  (`inr t) = checkInr Γ t σ τ <$> check Γ τ t
  check Γ (σ ⊗ τ)  (`inr t) = no $ λ p → case CHECK.proof p of λ ()
  check Γ (σ ─o τ) (`inr t) = no $ λ p → case CHECK.proof p of λ ()
  check Γ (κ n)    (`inr t) = no $ λ p → case CHECK.proof p of λ ()

