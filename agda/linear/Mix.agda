module linear.Mix where

open import Data.Fin as F
open import Data.Sum as Sum
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])

open import linear.Context as C
open import linear.Context.Pointwise as CP
open import linear.Context.Mix
open import linear.Usage as U hiding ([_])
open import linear.Usage.Pointwise as UP
open import linear.Usage.Mix
open import linear.Typing.Extensional

Mix : ∀ {T} → Typing T → Set
Mix {T} 𝓣 =
  ∀ {l m n o} {γ : Context l} {δ : Context m} {θ : Context n} {ξ : Context o}
  {Γ₁ Γ₂ Δ₁ Δ₂ Γ Γ′ Δ Δ′ t σ} {p : γ ++ δ ≅ θ} {q : γ ++ δ ≅ ξ} →
  [ p ] Γ₁ ++ Γ₂ ≅ Γ  → [ p ] Δ₁ ++ Δ₂ ≅ Δ → 
  [ q ] Γ₁ ++ Γ₂ ≅ Γ′ → [ q ] Δ₁ ++ Δ₂ ≅ Δ′ → 
  𝓣 Γ t σ Δ → ∃ λ t → 𝓣 Γ′ t σ Δ′

splitFin :
  ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p}
  {Γ₁ Γ₂ Δ₁ Δ₂ Γ Δ k σ} (p : γ ++ δ ≅ θ) →
  [ p ] Γ₁ ++ Γ₂ ≅ Γ → [ p ] Δ₁ ++ Δ₂ ≅ Δ →
  Γ ⊢ k ∈[ σ ]⊠ Δ → (∃ λ k → Γ₁ ⊢ k ∈[ σ ]⊠ Δ₁ × Γ₂ ≡ Δ₂)
                  ⊎ (∃ λ k → Γ₂ ⊢ k ∈[ σ ]⊠ Δ₂ × Γ₁ ≡ Δ₁)
splitFin [] [] [] ()
splitFin (σ ∷ˡ p) (_ ∷ˡ eq₁) (_  ∷ˡ eq₂) z
  rewrite proj₁ (≅-inj p eq₁ eq₂) = inj₁ (, z , proj₂ (≅-inj p eq₁ eq₂))
splitFin (σ ∷ʳ p) (_ ∷ʳ eq₁) (_  ∷ʳ eq₂) z
  rewrite proj₂ (≅-inj p eq₁ eq₂) = inj₂ (, z , proj₁ (≅-inj p eq₁ eq₂))
splitFin (σ ∷ˡ p) (u ∷ˡ eq₁) (.u ∷ˡ eq₂) (s K) =
  Sum.map
    (Prod.map F.suc (Prod.map s_ id))
    (Prod.map id (Prod.map id (cong (u ∷_))))
  $ splitFin p eq₁ eq₂ K
splitFin (σ ∷ʳ p) (u ∷ʳ eq₁) (.u ∷ʳ eq₂) (s K) =
  Sum.map
    (Prod.map id (Prod.map id (cong (u ∷_))))
    (Prod.map F.suc (Prod.map s_ id))
  $ splitFin p eq₁ eq₂ K

unsplitContext : ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p} (p : γ ++ δ ≅ θ) →
  ∃ λ (mM₁ : ∃ C.Mergey) →
  ∃ λ (mM₂ : ∃ C.Mergey) →
    Context[ _≡_ ] θ (γ C.⋈ proj₂ mM₁)
  × Context[ _≡_ ] θ (δ C.⋈ proj₂ mM₂)
unsplitContext []       = (, finish) , (, finish) , ([] , [])
unsplitContext (σ ∷ˡ p) =
  let ((_ , M₁) , (_ , M₂) , eq₁ , eq₂) = unsplitContext p
  in (, copy M₁) , (, insert σ M₂) , Eq.refl ∷ eq₁ , Eq.refl ∷ eq₂
unsplitContext (σ ∷ʳ p) =
  let ((m₁ , M₁) , (m₂ , M₂) , eq₁ , eq₂) = unsplitContext p
  in (, insert σ M₁) , (, copy M₂) , Eq.refl ∷ eq₁ , Eq.refl ∷ eq₂


unsplitUsages₁ :
  ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p}
  (p : γ ++ δ ≅ θ) (Δ : Usages δ) →
  let ((_ , M₁) , _) = unsplitContext p
  in U.Mergey M₁
unsplitUsages₁ []       Δ       = finish
unsplitUsages₁ (a ∷ˡ p) Δ       = copy (unsplitUsages₁ p Δ)
unsplitUsages₁ (a ∷ʳ p) (A ∷ Δ) = insert A (unsplitUsages₁ p Δ)

unsplitUsages₁-eq :
  ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p} {p : γ ++ δ ≅ θ} {Δ : Usages δ} →
  let ((_ , M₁) , _ , eq₁ , _) = unsplitContext p in
  ∀ {Γ Θ} → [ p ] Γ ++ Δ ≅ Θ → Usages[ _≡_ , UsageEq ] eq₁ Θ (Γ U.⋈ unsplitUsages₁ p Δ)
unsplitUsages₁-eq []        = []
unsplitUsages₁-eq (S ∷ˡ eq) = Eq.refl ∷ (unsplitUsages₁-eq eq)
unsplitUsages₁-eq (S ∷ʳ eq) = Eq.refl ∷ (unsplitUsages₁-eq eq)

unsplitUsages₂ :
  ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p} (p : γ ++ δ ≅ θ) (Γ : Usages γ) →
  let (_ , (_ , M₂) , _) = unsplitContext p
  in U.Mergey M₂
unsplitUsages₂ []       Γ       = finish
unsplitUsages₂ (a ∷ˡ p) (A ∷ Γ) = insert A (unsplitUsages₂ p Γ)
unsplitUsages₂ (a ∷ʳ p) Γ       = copy (unsplitUsages₂ p Γ)

unsplitUsages₂-eq :
  ∀ {m n p} {γ : Context m} {δ : Context n} {θ : Context p} {p : γ ++ δ ≅ θ} {Γ : Usages γ} →
  let (_ , (_ , M₂) , _ , eq₂) = unsplitContext p in
  ∀ {Δ Θ} → [ p ] Γ ++ Δ ≅ Θ → Usages[ _≡_ , UsageEq ] eq₂ Θ (Δ U.⋈ unsplitUsages₂ p Γ)
unsplitUsages₂-eq []        = []
unsplitUsages₂-eq (S ∷ˡ eq) = Eq.refl ∷ (unsplitUsages₂-eq eq)
unsplitUsages₂-eq (S ∷ʳ eq) = Eq.refl ∷ (unsplitUsages₂-eq eq)

mixFin : Mix TFin
mixFin {Γ₁ = Γ₁} {Γ₂} {p = p} {q} eqΓ eqΔ eqΓ′ eqΔ′ K =
  case splitFin p eqΓ eqΔ K of λ
  { (inj₁ (k , K , Γ₂≡Δ₂)) →
    let (_ , _ , eq₁ , _) = unsplitContext q
        inc               = unsplitUsages₁ q Γ₂
        EQΓ′              = unsplitUsages₁-eq eqΓ′
        EQΔ′              = unsplitUsages₁-eq eqΔ′
        K′                = U.weakFin inc K
        EQΔ′              = UP.irrelevance _ (subst _ (Eq.sym Γ₂≡Δ₂) (UP.sym EQΔ′))
    in , extensionalFin eq₁ (CP.sym eq₁) EQΓ′ EQΔ′ K′
  ; (inj₂ (k , K , Γ₁≡Δ₁)) →
    let (_ , _ , _ , eq₂) = unsplitContext q
        inc               = unsplitUsages₂ q Γ₁
        EQΓ′              = unsplitUsages₂-eq eqΓ′
        EQΔ′              = unsplitUsages₂-eq eqΔ′
        K′                = U.weakFin inc K
        EQΔ′              = UP.irrelevance _ (subst _ (Eq.sym Γ₁≡Δ₁) (UP.sym EQΔ′))
    in , extensionalFin eq₂ (CP.sym eq₂) EQΓ′ EQΔ′ K′
  }

