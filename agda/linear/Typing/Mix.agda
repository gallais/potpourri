module linear.Typing.Mix where

open import Data.Fin as F
open import Data.Sum as Sum
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])

open import linear.Context as C
open import linear.Context.Pointwise as CP
open import linear.Usage as U hiding ([_])
open import linear.Usage.Pointwise as UP
open import linear.Usage.Mix
open import linear.Language
open import linear.Typing
open import linear.Typing.Extensional

open import linear.Mix
open import linear.Context.Mix hiding (_++ˡ_)
open import linear.Usage.Mix

splitUsages :
  ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p}
  (p : γ ++ δ ≅ θ) (Γ : Usages θ) →
  ∃ λ Γ₁ → ∃ λ Γ₂ → [ p ] Γ₁ ++ Γ₂ ≅ Γ
splitUsages []       []      = [] , [] , []
splitUsages (a ∷ˡ p) (A ∷ Γ) =
  let (Γ₁ , Γ₂ , eq) = splitUsages p Γ
  in A ∷ Γ₁ , Γ₂ , A ∷ˡ eq
splitUsages (a ∷ʳ p) (A ∷ Γ) =
  let (Γ₁ , Γ₂ , eq) = splitUsages p Γ
  in Γ₁ , A ∷ Γ₂ , A ∷ʳ eq

unsplitUsages : ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p} (p : γ ++ δ ≅ θ)
  (Γ : Usages γ) (Δ : Usages δ) →
  ∃ λ Θ → [ p ] Γ ++ Δ ≅ Θ
unsplitUsages []       []      []      = , []
unsplitUsages (a ∷ˡ p) (A ∷ Γ) Δ       = Prod.map (A ∷_) (A ∷ˡ_) $ unsplitUsages p Γ Δ
unsplitUsages (a ∷ʳ p) Γ       (A ∷ Δ) = Prod.map (A ∷_) (A ∷ʳ_) $ unsplitUsages p Γ Δ

mutual

  mixCheck : Mix TCheck
  mixCheck eqΓ eqΔ eqΓ′ eqΔ′ (`lam b) =
    Prod.map `lam_ `lam_ $ mixCheck (_ ∷ˡ eqΓ) (_ ∷ˡ eqΔ) (_ ∷ˡ eqΓ′) (_ ∷ˡ eqΔ′) b
  mixCheck {p = p} {q} eqΓ eqΔ eqΓ′ eqΔ′ (`let pat ∷= t `in u) =
    let (Δ₁  , Δ₂  , eqΔ₁₂) = splitUsages p _
        (Δ′₁₂ , eqΔ′₁₂)     = unsplitUsages q Δ₁ Δ₂
        (t , T)             = mixInfer eqΓ eqΔ₁₂ eqΓ′ eqΔ′₁₂ t
        φ                   = patternContext pat
        (u , U)             = mixCheck ([[ φ ]] ++ˡ eqΔ₁₂)  (]] φ [[ ++ˡ eqΔ)
                                       ([[ φ ]] ++ˡ eqΔ′₁₂) (]] φ [[ ++ˡ eqΔ′) u
    in , `let pat ∷= T `in U
  mixCheck {p = p} {q} eqΓ eqΔ eqΓ′ eqΔ′ (`prd⊗ t u) =
    let (Δ₁  , Δ₂  , eqΔ₁₂) = splitUsages p _
        (Δ′₁₂ , eqΔ′₁₂)     = unsplitUsages q Δ₁ Δ₂
        (t , T)             = mixCheck eqΓ eqΔ₁₂ eqΓ′ eqΔ′₁₂ t
        (u , U)             = mixCheck eqΔ₁₂ eqΔ eqΔ′₁₂ eqΔ′ u
    in , `prd⊗ T U
  mixCheck eqΓ eqΔ eqΓ′ eqΔ′ (`prd& t u) =
    let (t , T) = mixCheck eqΓ eqΔ eqΓ′ eqΔ′ t
        (u , U) = mixCheck eqΓ eqΔ eqΓ′ eqΔ′ u
    in , `prd& T U
  mixCheck eqΓ eqΔ eqΓ′ eqΔ′ (`inl t) = Prod.map `inl_ `inl_ $ mixCheck eqΓ eqΔ eqΓ′ eqΔ′ t
  mixCheck eqΓ eqΔ eqΓ′ eqΔ′ (`inr t) = Prod.map `inr_ `inr_ $ mixCheck eqΓ eqΔ eqΓ′ eqΔ′ t
  mixCheck eqΓ eqΔ eqΓ′ eqΔ′ (`neu t) = Prod.map `neu_ `neu_ $ mixInfer eqΓ eqΔ eqΓ′ eqΔ′ t

  mixInfer : Mix TInfer
  mixInfer eqΓ eqΔ eqΓ′ eqΔ′ (`var k) = Prod.map `var_ `var_ $ mixFin eqΓ eqΔ eqΓ′ eqΔ′ k
  mixInfer {p = p} {q} eqΓ eqΔ eqΓ′ eqΔ′ (`app f t) =
    let (Δ₁  , Δ₂  , eqΔ₁₂) = splitUsages p _
        (Δ′₁₂ , eqΔ′₁₂)     = unsplitUsages q Δ₁ Δ₂
        (f , F)             = mixInfer eqΓ eqΔ₁₂ eqΓ′ eqΔ′₁₂ f
        (t , T)             = mixCheck eqΔ₁₂ eqΔ eqΔ′₁₂ eqΔ′ t
    in , `app F T
  mixInfer eqΓ eqΔ eqΓ′ eqΔ′ (`fst p) = Prod.map `fst_ `fst_ $ mixInfer eqΓ eqΔ eqΓ′ eqΔ′ p
  mixInfer eqΓ eqΔ eqΓ′ eqΔ′ (`snd p) = Prod.map `snd_ `snd_ $ mixInfer eqΓ eqΔ eqΓ′ eqΔ′ p
  mixInfer {p = p} {q} eqΓ eqΔ eqΓ′ eqΔ′ (`case t return σ of l %% r) =
    let (Δ₁  , Δ₂  , eqΔ₁₂) = splitUsages p _
        (Δ′₁₂ , eqΔ′₁₂)     = unsplitUsages q Δ₁ Δ₂
        (t , T)             = mixInfer eqΓ eqΔ₁₂ eqΓ′ eqΔ′₁₂ t
        (l , L)             = mixCheck (_ ∷ˡ eqΔ₁₂) (_ ∷ˡ eqΔ) (_ ∷ˡ eqΔ′₁₂) (_ ∷ˡ eqΔ′) l
        (r , R)             = mixCheck (_ ∷ˡ eqΔ₁₂) (_ ∷ˡ eqΔ) (_ ∷ˡ eqΔ′₁₂) (_ ∷ˡ eqΔ′) r
    in , `case T return σ of L %% R
  mixInfer eqΓ eqΔ eqΓ′ eqΔ′ (`cut t) = Prod.map _ `cut $ mixCheck eqΓ eqΔ eqΓ′ eqΔ′ t
