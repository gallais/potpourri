module linear.Completeness where

open import Data.Nat
import Data.Fin as F
open import Data.Nat.Properties.Simple
open import Data.List as List hiding ([_] ; _∷ʳ_)
open import Data.List.Properties
open import Data.Vec hiding ([_] ; _∷ʳ_)
open import Data.Product as Prod
open import Data.Sum as Sum
open import Function
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])


open import linear.ILL
open import linear.Type
open import linear.Context as C
open import linear.Scope as S
open import linear.Usage as U hiding ([_])
open import linear.Usage.Erasure
open import linear.Context.Pointwise as CP
open import linear.Usage.Pointwise as UP
open import linear.Language as L
open import linear.Typing
open import linear.Typing.Extensional
open import linear.Typing.Substitution as T

lemma₁ : ∀ (γ : List Type) δ → S.Mergey (length γ) (length (δ List.++ γ))
lemma₁ γ []      = finish
lemma₁ γ (σ ∷ δ) = insert (lemma₁ γ δ)

Lemma₁ : ∀ γ δ → C.Mergey (lemma₁ γ δ)
Lemma₁ γ []      = finish
Lemma₁ γ (σ ∷ δ) = insert σ (Lemma₁ γ δ)

Lemma₁-eq : ∀ γ δ → Context[ _≡_ ] (fromList (δ List.++ γ)) (fromList γ C.⋈ Lemma₁ γ δ)
Lemma₁-eq γ []      = CP.refl
Lemma₁-eq γ (σ ∷ δ) = Eq.refl ∷ Lemma₁-eq γ δ

𝓛emma₁ :  ∀ γ δ (Δ : Usages (fromList δ)) → U.Mergey (Lemma₁ γ δ)
𝓛emma₁ γ []      []      = finish
𝓛emma₁ γ (σ ∷ δ) (S ∷ Δ) = insert S (𝓛emma₁ γ δ Δ)

𝓛emma₁-[[eq]] : ∀ γ δ → Usages[ _≡_ , UsageEq ] (Lemma₁-eq γ δ)
                        [[ fromList (δ List.++ γ) ]]
                        ([[ fromList γ ]] U.⋈ 𝓛emma₁ γ δ [[ fromList δ ]])
𝓛emma₁-[[eq]] γ []      = UP.refl
𝓛emma₁-[[eq]] γ (σ ∷ δ) = Eq.refl ∷ 𝓛emma₁-[[eq]] γ δ

𝓛emma₁-]]eq[[ : ∀ γ δ → Usages[ _≡_ , UsageEq ] (Lemma₁-eq γ δ)
                        ]] fromList (δ List.++ γ) [[
                        (]] fromList γ [[ U.⋈ 𝓛emma₁ γ δ ]] fromList δ [[)
𝓛emma₁-]]eq[[ γ []      = UP.refl
𝓛emma₁-]]eq[[ γ (σ ∷ δ) = Eq.refl ∷ 𝓛emma₁-]]eq[[ γ δ

lemma₂ : ∀ (γ : List Type) δ → S.Mergey (length γ) (length (γ List.++ δ))
lemma₂ []      []      = finish
lemma₂ []      (σ ∷ δ) = insert (lemma₂ [] δ)
lemma₂ (σ ∷ γ) δ       = copy (lemma₂ γ δ)

Lemma₂ : ∀ γ δ → C.Mergey (lemma₂ γ δ)
Lemma₂ []      []      = finish
Lemma₂ []      (σ ∷ δ) = insert σ (Lemma₂ [] δ)
Lemma₂ (σ ∷ γ) δ       = copy (Lemma₂ γ δ)

Lemma₂-eq : ∀ γ δ → Context[ _≡_ ] (fromList (γ List.++ δ)) (fromList γ C.⋈ Lemma₂ γ δ)
Lemma₂-eq []      []      = []
Lemma₂-eq []      (σ ∷ δ) = Eq.refl ∷ Lemma₂-eq [] δ
Lemma₂-eq (σ ∷ γ) δ       = Eq.refl ∷ Lemma₂-eq γ δ

Lemma₁₂-eq : ∀ γ δ → Context[ _≡_ ] (fromList δ C.⋈ Lemma₁ δ γ)
                                    (fromList γ C.⋈ Lemma₂ γ δ)
Lemma₁₂-eq γ δ = CP.trans (CP.sym (Lemma₁-eq δ γ)) (Lemma₂-eq γ δ)

Lemma₂₁-eq : ∀ γ δ → Context[ _≡_ ] (fromList γ C.⋈ Lemma₂ γ δ)
                                    (fromList δ C.⋈ Lemma₁ δ γ)
Lemma₂₁-eq γ δ = CP.trans (CP.sym (Lemma₂-eq γ δ)) (Lemma₁-eq δ γ)

𝓛emma₂ :  ∀ γ δ (Δ : Usages (fromList δ)) → U.Mergey (Lemma₂ γ δ)
𝓛emma₂ []      []      Δ       = finish
𝓛emma₂ []      (σ ∷ δ) (S ∷ Δ) = insert S (𝓛emma₂ [] δ Δ)
𝓛emma₂ (σ ∷ γ) δ       Δ       = copy (𝓛emma₂ γ δ Δ)

𝓛emma₂-[[eq]] : ∀ γ δ → Usages[ _≡_ , UsageEq ] (Lemma₂-eq γ δ)
                        [[ fromList (γ List.++ δ) ]]
                        ([[ fromList γ ]] U.⋈ 𝓛emma₂ γ δ [[ fromList δ ]])
𝓛emma₂-[[eq]] []      []      = []
𝓛emma₂-[[eq]] []      (σ ∷ δ) = Eq.refl ∷ 𝓛emma₂-[[eq]] [] δ
𝓛emma₂-[[eq]] (x ∷ γ) δ       = Eq.refl ∷ 𝓛emma₂-[[eq]] γ δ

𝓛emma₂-]]eq[[ : ∀ γ δ → Usages[ _≡_ , UsageEq ] (Lemma₂-eq γ δ)
                        ]] fromList (γ List.++ δ) [[
                        (]] fromList γ [[ U.⋈ 𝓛emma₂ γ δ ]] fromList δ [[)
𝓛emma₂-]]eq[[ []      []      = []
𝓛emma₂-]]eq[[ []      (σ ∷ δ) = Eq.refl ∷ 𝓛emma₂-]]eq[[ [] δ
𝓛emma₂-]]eq[[ (σ ∷ γ) δ       = Eq.refl ∷ 𝓛emma₂-]]eq[[ γ δ

𝓛emma₁₂-]]eq[[ : ∀ γ δ → Usages[ _≡_ , UsageEq ] (Lemma₁₂-eq γ δ)
                         (]] fromList δ [[ U.⋈ 𝓛emma₁ δ γ [[ fromList γ ]])
                         ([[ fromList γ ]] U.⋈ 𝓛emma₂ γ δ ]] fromList δ [[)
𝓛emma₁₂-]]eq[[ (σ ∷ γ) δ       = Eq.refl ∷ 𝓛emma₁₂-]]eq[[ γ δ
𝓛emma₁₂-]]eq[[ []      []      = UP.refl
𝓛emma₁₂-]]eq[[ []      (σ ∷ δ) = Eq.refl ∷ 𝓛emma₁₂-]]eq[[ [] δ

𝓛emma₁₂-[[eq]] : ∀ γ δ → Usages[ _≡_ , UsageEq ] (Lemma₁₂-eq γ δ)
                         ([[ fromList δ ]] U.⋈ 𝓛emma₁ δ γ ]] fromList γ [[)
                         (]] fromList γ [[ U.⋈ 𝓛emma₂ γ δ [[ fromList δ ]])
𝓛emma₁₂-[[eq]] (σ ∷ γ) δ       = Eq.refl ∷ 𝓛emma₁₂-[[eq]] γ δ
𝓛emma₁₂-[[eq]] []      []      = UP.refl
𝓛emma₁₂-[[eq]] []      (σ ∷ δ) = Eq.refl ∷ 𝓛emma₁₂-[[eq]] [] δ

𝓛emma₂₁-[[eq]] : ∀ γ δ → Usages[ _≡_ , UsageEq ] (Lemma₂₁-eq γ δ)
                         ([[ fromList γ ]] U.⋈ 𝓛emma₂ γ δ [[ fromList δ ]])
                         ([[ fromList δ ]] U.⋈ 𝓛emma₁ δ γ [[ fromList γ ]])
𝓛emma₂₁-[[eq]] (σ ∷ γ) δ       = Eq.refl ∷ 𝓛emma₂₁-[[eq]] γ δ
𝓛emma₂₁-[[eq]] []      []      = []
𝓛emma₂₁-[[eq]] []      (σ ∷ δ) = Eq.refl ∷ 𝓛emma₂₁-[[eq]] [] δ

𝓛emma₂₁-]]eq[[ : ∀ γ δ → Usages[ _≡_ , UsageEq ] (Lemma₂₁-eq γ δ)
                         (]] fromList γ [[ U.⋈ 𝓛emma₂ γ δ [[ fromList δ ]])
                         ([[ fromList δ ]] U.⋈ 𝓛emma₁ δ γ ]] fromList γ [[)
𝓛emma₂₁-]]eq[[ (σ ∷ γ) δ       = Eq.refl ∷ 𝓛emma₂₁-]]eq[[ γ δ
𝓛emma₂₁-]]eq[[ []      []      = []
𝓛emma₂₁-]]eq[[ []      (σ ∷ δ) = Eq.refl ∷ 𝓛emma₂₁-]]eq[[ [] δ


complete : {γ : List Type} {σ : Type} → γ ⊢ σ →
           ∃ λ t → [[ fromList γ ]] ⊢ σ ∋ t ⊠ ]] fromList γ [[
complete ax         = , `neu (`var z)
complete (cut {γ} {δ} {σ} {τ} t u)  =
  let (rT , T) = complete t
      (rU , U) = complete u

      U′ : [[ fromList (σ ∷ δ) ]] U.⋈ copy (𝓛emma₁ δ γ [[ fromList γ ]])
           ⊢ τ ∋ _ ⊠
           ]] fromList (σ ∷ δ) [[ U.⋈ copy (𝓛emma₁ δ γ [[ fromList γ ]])
      U′ = T.weakCheck (copy (𝓛emma₁ δ γ [[ fromList γ ]])) U

      T′ : [[ fromList γ ]] U.⋈ 𝓛emma₂ γ δ ]] fromList δ [[
           ⊢ σ ∋ _ ⊠
           ]] fromList γ [[ U.⋈ 𝓛emma₂ γ δ ]] fromList δ [[
      T′ = T.weakCheck (𝓛emma₂ γ δ ]] fromList δ [[) T

      F : [[ fromList γ ]] U.⋈ 𝓛emma₂ γ δ [[ fromList δ ]]
          ⊢ _ ∈ σ ─o τ ⊠
          [[ fromList γ ]] U.⋈ 𝓛emma₂ γ δ ]] fromList δ [[
      F = extensionalInfer (Lemma₂₁-eq γ δ) (Lemma₁₂-eq γ δ)
          (𝓛emma₂₁-[[eq]] γ δ) (𝓛emma₁₂-]]eq[[ γ δ)
        $ `cut (`lam U′)

      FT : [[ fromList (γ List.++ δ) ]]
           ⊢ _ ∈ τ ⊠
           ]] fromList (γ List.++ δ) [[
      FT = extensionalInfer (Lemma₂-eq γ δ) (CP.sym (Lemma₂-eq γ δ))
           (𝓛emma₂-[[eq]] γ δ) (UP.sym (𝓛emma₂-]]eq[[ γ δ))
         $ `app F T′

  in , `neu FT
complete (⊗R {γ} {δ} {σ} {τ} t u)   =
  let (rT , T) = complete t
      (rU , U) = complete u
      
      T′ : [[ fromList δ ]] U.⋈ 𝓛emma₁ δ γ [[ fromList γ ]]
           ⊢ σ ∋ _ ⊠
           [[ fromList δ ]] U.⋈ 𝓛emma₁ δ γ ]] fromList γ [[
      T′ = extensionalCheck (Lemma₁₂-eq γ δ) (Lemma₂₁-eq γ δ)
           (UP.irrelevance _ (UP.sym (𝓛emma₂₁-[[eq]] γ δ)))
           (𝓛emma₂₁-]]eq[[ γ δ)
         $ T.weakCheck (𝓛emma₂ γ δ [[ fromList δ ]]) T
      
      U′ : [[ fromList δ ]] U.⋈ 𝓛emma₁ δ γ ]] fromList γ [[
           ⊢ τ ∋ _ ⊠
           ]] fromList δ [[ U.⋈ 𝓛emma₁ δ γ ]] fromList γ [[
      U′ = T.weakCheck (𝓛emma₁ δ γ ]] fromList γ [[) U

      TU : [[ fromList (γ List.++ δ) ]]
           ⊢ σ ⊗ τ ∋ _ ⊠
           ]] fromList (γ List.++ δ) [[
      TU = extensionalCheck (Lemma₁-eq δ γ) (CP.sym (Lemma₁-eq δ γ))
           (𝓛emma₁-[[eq]] δ γ) (UP.sym (𝓛emma₁-]]eq[[ δ γ))
         $ `prd⊗ T′ U′

  in , TU
complete (⊗L t)     =
  let (rT , T) = complete t
      T′       = T.weakCheck (copy (copy (U.inserts (_ ∷ _ ∷ _ ∷ []) finish))) T
  in , `let `v ,, `v ∷= `var z
       `in `neu `app (`app (`cut (`lam (`lam T′))) (`neu `var z)) (`neu (`var (s z)))
complete (─oR t)    = , `lam (proj₂ $ complete t)
complete (─oL {γ} {δ} {σ} {τ} {ν} t u)  =
  let (rT , T) = complete t
      (rU , U) = complete u

      U′ : [[ fromList ((σ ─o τ) ∷ γ) ]] U.⋈ 𝓛emma₂ ((σ ─o τ) ∷ γ) δ [[ fromList δ ]]
           ⊢ τ ─o ν ∋ _ ⊠
           [[ fromList ((σ ─o τ) ∷ γ) ]] U.⋈ 𝓛emma₂ ((σ ─o τ) ∷ γ) δ ]] fromList δ [[
      U′ = extensionalCheck (Lemma₂₁-eq ((σ ─o τ) ∷ γ) δ) (Lemma₁₂-eq ((σ ─o τ) ∷ γ) δ)
           (𝓛emma₂₁-[[eq]] ((σ ─o τ) ∷ γ) δ) (𝓛emma₁₂-]]eq[[ ((σ ─o τ) ∷ γ) δ)
         $ T.weakCheck (𝓛emma₁ δ ((σ ─o τ) ∷ γ) [[ fromList ((σ ─o τ) ∷ γ) ]]) (`lam U)

      T′ : ] σ ─o τ [ ∷ ([[ fromList γ ]] U.⋈ 𝓛emma₂ γ δ ]] fromList δ [[)
           ⊢ σ ∋ _ ⊠
           ] σ ─o τ [ ∷ (]] fromList γ [[ U.⋈ 𝓛emma₂ γ δ ]] fromList δ [[)
      T′ = T.weakCheck (insert _ (𝓛emma₂ γ δ ]] fromList δ [[)) T

      UT : [[ fromList ((σ ─o τ) ∷ γ List.++ δ) ]]
           ⊢ _ ∈ ν ⊠
           ]] fromList ((σ ─o τ) ∷ γ List.++ δ) [[
      UT = extensionalInfer (Eq.refl ∷ Lemma₂-eq γ δ) (Eq.refl ∷ CP.sym (Lemma₂-eq γ δ))
           (Eq.refl ∷ 𝓛emma₂-[[eq]] γ δ)
           (Eq.refl ∷ UP.sym (𝓛emma₂-]]eq[[ γ δ))
         $ `app (`cut U′) (`neu (`app (`var z) T′))

  in , `neu UT
complete (&R t u)   = , `prd& (proj₂ $ complete t) (proj₂ $ complete u)
complete (&₁L t)    =
  let (rT , T) = complete t
      T′       = T.weakCheck (copy (insert _ finish)) T
  in , `neu `app (`cut (`lam T′)) (`neu (`fst (`var z)))
complete (&₂L t)    =
  let (rT , T) = complete t
      T′       = T.weakCheck (copy (insert _ finish)) T
  in , `neu `app (`cut (`lam T′)) (`neu (`snd (`var z)))
complete (⊕₁R t)    = , `inl (proj₂ $ complete t)
complete (⊕₂R t)    = , `inr (proj₂ $ complete t)
complete (⊕L t u)   =
  let (rT , T) = complete t
      (rU , U) = complete u
      T′       = T.weakCheck (copy (insert _ finish)) T
      U′       = T.weakCheck (copy (insert _ finish)) U
  in , `neu (`case `var z return _ of T′ %% U′)
complete (mix t inc) = {!!} -- mixCheck inc $ proj₂ $ complete t


infix 5 [_]_++_≅_ 
data [_]_++_≅_ :
  ∀ {γ δ θ} → γ ++ δ ≅ θ →
  Usages (fromList γ) → Usages (fromList δ) → Usages (fromList θ) →
  Set where
  []   : [ [] ] [] ++ [] ≅ []
  _∷ˡ_ : ∀ {σ γ δ θ} {p : γ ++ δ ≅ θ} {Γ Δ Θ} (S : Usage σ) →
         [ p ] Γ ++ Δ ≅ Θ → [ σ ∷ˡ p ] S ∷ Γ ++ Δ ≅ S ∷ Θ
  _∷ʳ_ : ∀ {σ γ δ θ} {p : γ ++ δ ≅ θ} {Γ Δ Θ} (S : Usage σ) →
         [ p ] Γ ++ Δ ≅ Θ → [ σ ∷ʳ p ] Γ ++ S ∷ Δ ≅ S ∷ Θ

split-Usages :
  ∀ {γ δ θ} (p : γ ++ δ ≅ θ) (Γ : Usages (fromList θ)) →
  ∃ λ Γ₁ → ∃ λ Γ₂ → [ p ] Γ₁ ++ Γ₂ ≅ Γ
split-Usages []       []      = [] , [] , []
split-Usages (a ∷ˡ p) (A ∷ Γ) =
  let (Γ₁ , Γ₂ , eq) = split-Usages p Γ
  in A ∷ Γ₁ , Γ₂ , A ∷ˡ eq
split-Usages (a ∷ʳ p) (A ∷ Γ) =
  let (Γ₁ , Γ₂ , eq) = split-Usages p Γ
  in Γ₁ , A ∷ Γ₂ , A ∷ʳ eq


≅-inj : ∀ {γ δ θ Γ₁ Γ₂ Δ₁ Δ₂ Θ} (p : γ ++ δ ≅ θ) →
  [ p ] Γ₁ ++ Δ₁ ≅ Θ → [ p ] Γ₂ ++ Δ₂ ≅ Θ →
  Γ₁ ≡ Γ₂ × Δ₁ ≡ Δ₂
≅-inj []       []         []          = Eq.refl , Eq.refl
≅-inj (a ∷ˡ p) (S ∷ˡ eq₁) (.S ∷ˡ eq₂) = Prod.map (cong (S ∷_)) id $ ≅-inj p eq₁ eq₂
≅-inj (σ ∷ʳ p) (S ∷ʳ eq₁) (.S ∷ʳ eq₂) = Prod.map id (cong (S ∷_)) $ ≅-inj p eq₁ eq₂

splitFin :
  ∀ {γ δ θ Γ₁ Γ₂ Δ₁ Δ₂ Γ Δ k σ} (p : γ ++ δ ≅ θ) →
  [ p ] Γ₁ ++ Γ₂ ≅ Γ → [ p ] Δ₁ ++ Δ₂ ≅ Δ →
  Γ ⊢ k ∈[ σ ]⊠ Δ → (∃ λ k → Γ₁ ⊢ k ∈[ σ ]⊠ Δ₁)
                  ⊎ (∃ λ k → Γ₂ ⊢ k ∈[ σ ]⊠ Δ₂)
splitFin [] [] [] ()
splitFin (σ ∷ˡ p) (_ ∷ˡ eq₁) (_  ∷ˡ eq₂) z
  rewrite proj₁ (≅-inj p eq₁ eq₂) = inj₁ (, z)
splitFin (σ ∷ʳ p) (_ ∷ʳ eq₁) (_  ∷ʳ eq₂) z
  rewrite proj₂ (≅-inj p eq₁ eq₂) = inj₂ (, z)
splitFin (σ ∷ˡ p) (u ∷ˡ eq₁) (.u ∷ˡ eq₂) (s K) =
  Sum.map (Prod.map _ s_) id $ splitFin p eq₁ eq₂ K
splitFin (σ ∷ʳ p) (u ∷ʳ eq₁) (.u ∷ʳ eq₂) (s K) =
  Sum.map id (Prod.map _ s_) $ splitFin p eq₁ eq₂ K

-- Is this the right thing?
Mix : ∀ {T} → Typing T → Set
Mix {T} 𝓣 =
  ∀ {γ δ θ Γ₁ Γ₂ Δ₁ Δ₂ Γ Γ′ Δ Δ′ t σ} (p q : γ ++ δ ≅ θ) →
  [ p ] Γ₁ ++ Γ₂ ≅ Γ  → [ p ] Δ₁ ++ Δ₂ ≅ Δ → 
  [ q ] Γ₁ ++ Γ₂ ≅ Γ′ → [ q ] Δ₁ ++ Δ₂ ≅ Δ′ → 
  𝓣 Γ t σ Δ → ∃ λ t → 𝓣 Γ′ t σ Δ′

