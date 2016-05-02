module linear.Typing.Thinning where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Vec hiding (map ; tail)
open import Function
open import Relation.Binary.PropositionalEquality

open import linear.Type
open import linear.Scope as Sc
open import linear.Context as C
open import linear.Usage as U hiding (tail)
open import linear.Usage.Consumption using (weaken⁻¹ ; tail ; truncate)
open import linear.Language
open import linear.Typing
open import linear.Typing.Consumption

Thinning : {T : ℕ → Set} (Wk : Sc.Weakening T) (𝓣 : Typing T) → Set
Thinning {T} Wk 𝓣 =
  {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} (𝓜 : U.Mergey M) →
  {γ : Context k} (Γ Δ : Usages γ) {t : T l} {σ : Type} →
  𝓣 (Γ U.⋈ 𝓜) t σ (Δ U.⋈ 𝓜) → Σ[ t′ ∈ T k ] t ≡ Wk m t′ × 𝓣 Γ t′ σ Δ

data Usages[_]
  {ℓ^R : Level} (R : {σ : Type} (S T : Usage σ) → Set ℓ^R) :
  {k : ℕ} {γ : Context k} → Usages γ → Usages γ → Set ℓ^R where
  []  : Usages[ R ] [] []
  _∷_ : {k : ℕ} {γ : Context k} {Γ Δ : Usages γ} {σ : Type} {S T : Usage σ} →
        R S T → Usages[ R ] Γ Δ → Usages[ R ] (S ∷ Γ) (T ∷ Δ)

reflUsages : {k : ℕ} {γ : Context k} (Γ : Usages γ) → Usages[ _≡_ ] Γ Γ
reflUsages []      = []
reflUsages (x ∷ Γ) = refl ∷ reflUsages Γ

equalUsages : {k : ℕ} {γ : Context k} {Γ Δ : Usages γ} → Usages[ _≡_ ] Γ Δ → Γ ≡ Δ
equalUsages []           = refl
equalUsages (refl ∷ eqs) = cong (_∷_ _) (equalUsages eqs)

Thinning′ : {T : ℕ → Set} (Wk : Sc.Weakening T) (𝓣 : Typing T) → Set
Thinning′ {T} Wk 𝓣 =
  {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} (𝓜 : U.Mergey M) →
  {γ : Context k} {Γ Δ : Usages γ} {ξ ζ : Usages (γ C.⋈ M)} {t : T l} {σ : Type} →
  Usages[ _≡_ ] ξ (Γ U.⋈ 𝓜) → Usages[ _≡_ ] ζ (Δ U.⋈ 𝓜) →
  
  𝓣 ξ t σ ζ → Σ[ t′ ∈ T k ] t ≡ Wk m t′ × 𝓣 Γ t′ σ Δ

thinning : {T : ℕ → Set} {Wk : Sc.Weakening T} {𝓣 : Typing T} → Thinning′ Wk 𝓣 → Thinning Wk 𝓣
thinning th 𝓜 Γ Δ t = th 𝓜 (reflUsages _) (reflUsages _) t

thinning′Fin : Thinning′ Sc.weakFin TFin
thinning′Fin finish Γ Δ k rewrite equalUsages Γ | equalUsages Δ = , refl , k
thinning′Fin (copy 𝓜) {γ = σ ∷ γ} {Γ = _ ∷ Γ} {Δ = _ ∷ Δ} (refl ∷ eqΓ) (refl ∷ eqΔ) z
  rewrite ⋈ˡ-injective (_ , _ , _ , _ , _ , 𝓜 , _) (equalUsages eqΓ) (equalUsages eqΔ) =
  Fin.zero , refl , z
thinning′Fin (copy 𝓜) {γ = σ ∷ γ} {S ∷ Γ} {T ∷ Δ} (eqS ∷ eqΓ) (eqT ∷ eqΔ) (s k)
  rewrite trans (sym eqS) eqT =
  let (k′ , eq , K) = thinning′Fin 𝓜 eqΓ eqΔ k
  in Fin.suc k′ , cong Fin.suc eq , s K
thinning′Fin (insert A 𝓜) (S ∷ Γ) (T ∷ Δ) (s k) =
  let (k′ , eq , K) = thinning′Fin 𝓜 Γ Δ k
  in k′ , cong Fin.suc eq , K
thinning′Fin (insert A 𝓜) (S ∷ Γ) (T ∷ Δ) z = case trans S (sym T) of λ ()

thinningFin : Thinning Sc.weakFin TFin
thinningFin = thinning thinning′Fin 

mutual

  thinningInfer : Thinning weakInfer TInfer
  thinningInfer 𝓜 Γ Δ (`var k)     =
    let (k′ , eq , K) = thinningFin 𝓜 Γ Δ k
    in `var k′ , cong `var eq , `var K
  thinningInfer 𝓜 Γ Δ (`app f t) =
    let (χ , eq)       = weaken⁻¹ 𝓜 (consumptionInfer f) (consumptionCheck t)
        (f′ , eqf , F) = thinningInfer 𝓜 Γ _ (subst (_ ⊢ _ ∈ _ ⊠_) eq f)
        (t′ , eqt , T) = thinningCheck 𝓜 _ Δ (subst (_⊢ _ ∋ _ ⊠ _) eq t)
    in `app f′ t′ , cong₂ `app eqf eqt , `app F T
  thinningInfer 𝓜 Γ Δ (`case_return_of_%%_ {σ} {τ} {rχ} .{Δ U.⋈ 𝓜} {rt} {rl} {rr} t ν l r) =
    let (χ , eq)       = weaken⁻¹ 𝓜 (consumptionInfer t) (tail $ consumptionCheck l)
        (t′ , eqt , T) = thinningInfer 𝓜 Γ _ (subst (_ ⊢ _ ∈ _ ⊠_) eq t)
        coerced-l : U.[ σ ] ∷ (χ U.⋈ 𝓜) ⊢ ν ∋ rl ⊠ U.] σ [ ∷ (Δ U.⋈ 𝓜)
        coerced-l = subst (_⊢ ν ∋ rl ⊠ U.] σ [ ∷ (Δ U.⋈ 𝓜)) (cong (U.[ σ ] ∷_) eq) l
        coerced-r : U.[ τ ] ∷ (χ U.⋈ 𝓜) ⊢ ν ∋ rr ⊠ U.] τ [ ∷ (Δ U.⋈ 𝓜)
        coerced-r = subst (_⊢ ν ∋ rr ⊠ U.] τ [ ∷ (Δ U.⋈ 𝓜)) (cong (U.[ τ ] ∷_) eq) r
        (l′ , eql , L) = thinningCheck (copy 𝓜) _ _ coerced-l
        (r′ , eqr , R) = thinningCheck (copy 𝓜) _ _ coerced-r
    in `case t′ return ν of l′ %% r′
     , cong₂ (λ t lr → `case t return ν of proj₁ lr %% proj₂ lr) eqt (cong₂ _,_ eql eqr)
     , `case T return ν of L %% R
  thinningInfer 𝓜 Γ Δ (`cut t) =
    let (t′ , eq , T) = thinningCheck 𝓜 Γ Δ t
    in `cut t′ _ , cong (λ t → `cut t _) eq , `cut T

  thinningCheck : Thinning weakCheck TCheck
  thinningCheck 𝓜 Γ Δ (`lam b) =
    let (b′ , eqb , B) = thinningCheck (copy 𝓜) (U.[ _ ] ∷ Γ) (U.] _ [ ∷ Δ) b
    in `lam b′ , cong `lam_ eqb , `lam B
  thinningCheck 𝓜 Γ Δ (`let_∷=_`in_ {σ} {τ} {o} {rp} {δ} {rt} {rχ} .{Δ U.⋈ 𝓜} {ru} p t u) =
    let (χ , eq)       = weaken⁻¹ 𝓜 (consumptionInfer t) (truncate (patternContext p) (consumptionCheck u))
        (t′ , eqt , T) = thinningInfer 𝓜 Γ χ (subst (_ ⊢ _ ∈ _ ⊠_) eq t)
        coerced-u      : ([[ δ ]] U.++ χ) U.⋈ U.copys o 𝓜 ⊢ τ ∋ ru ⊠ (]] δ [[ U.++ Δ) U.⋈ U.copys o 𝓜
        coerced-u      = {!!} -- hard!
        (u′ , equ , U) = thinningCheck (U.copys o 𝓜) ([[ δ ]] U.++ χ) (]] δ [[ U.++ Δ) coerced-u
    in `let rp ∷= t′ `in u′
     , cong₂ (`let rp ∷=_`in_) eqt equ
     , `let p ∷= T `in U
  thinningCheck 𝓜 Γ Δ (`prd a b) =
    let (χ , eq)       = weaken⁻¹ 𝓜 (consumptionCheck a) (consumptionCheck b)
        (a′ , eqa , A) = thinningCheck 𝓜 Γ χ (subst (_ ⊢ _ ∋ _ ⊠_) eq a)
        (b′ , eqb , B) = thinningCheck 𝓜 χ Δ (subst (_⊢ _ ∋ _ ⊠ _) eq b)
    in `prd a′ b′ , cong₂ `prd eqa eqb , `prd A B
  thinningCheck 𝓜 Γ Δ (`inl t) =
    let (t′ , eq , T) = thinningCheck 𝓜 Γ Δ t
    in `inl t′ , cong `inl_ eq , `inl T
  thinningCheck 𝓜 Γ Δ (`inr t) =
    let (t′ , eq , T) = thinningCheck 𝓜 Γ Δ t
    in `inr t′ , cong `inr_ eq , `inr T
  thinningCheck 𝓜 Γ Δ (`neu t) = 
    let (t′ , eq , T) = thinningInfer 𝓜 Γ Δ t
    in `neu t′ , cong `neu_ eq , `neu T
