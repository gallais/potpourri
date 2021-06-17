module poc.Telescope where

open import Level using (_⊔_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product
open import Data.Unit.Polymorphic.Base
open import Function.Base using (_∘_)
open import Function.Nary.NonDependent.Base using (Levels; ⨆)

module Left where

  Sets : ∀ n (ls : Levels n) → Set (Level.suc (⨆ n ls))
  Tele : ∀ n {ls} → Sets n ls → Set (⨆ n ls)

  Sets zero    ls       = ⊤
  Sets (suc n) (l , ls) = Σ[ Γ ∈ Sets n ls ] (Tele n Γ → Set l)

  Tele zero    _       = ⊤
  Tele (suc n) (Γ , A) = Σ[ γ ∈ Tele n Γ ] (A γ)

  open import Function.Base using (_∘_)

  EqSets : ∀ ℓ → Sets 3 _
  EqSets ℓ = ((_ , (λ _ → Set ℓ)) , proj₂) , proj₂ ∘ proj₁

  Arrows : ∀  n {ls} → (Γ : Sets n ls) →
           ∀ {r} (R : Tele n Γ → Set r) →
           Set (r ⊔ ⨆ n ls)
  Arrows zero    Γ       R = R _
  Arrows (suc n) (Γ , A) R = Arrows n Γ λ γ → (a : A γ) → R (γ , a)

  open import Agda.Builtin.Equality

  Eq : ∀ {ℓ} → Arrows 3 (EqSets ℓ) (λ _ → Set ℓ)
  Eq A = _≡_

module Right where

  -- Note that here the definitions do not need to be mutual

  Sets : ∀ n (ls : Levels n) → Set (Level.suc (⨆ n ls))
  Sets zero    ls       = ⊤
  Sets (suc n) (l , ls) = Σ[ A ∈ Set l ] (A → Sets n ls)

  Tele : ∀ n {ls} → Sets n ls → Set (⨆ n ls)
  Tele zero    _       = ⊤
  Tele (suc n) (A , Γ) = Σ[ a ∈ A ] (Tele n (Γ a))

  Arrows : ∀  n {ls} → (Γ : Sets n ls) →
           ∀ {r} (R : Tele n Γ → Set r) →
           Set (r ⊔ ⨆ n ls)
  Arrows zero    Γ       R = R _
  Arrows (suc n) (A , Γ) R = (a : A) → Arrows n (Γ a) (R ∘ (a ,_))

  open import Function.Base using (_∘_)

  EqSets : ∀ ℓ → Sets 3 _
  EqSets ℓ = Set ℓ , λ A → A , λ _ → A , _

  open import Agda.Builtin.Equality

  Eq : ∀ {ℓ} → Arrows 3 (EqSets ℓ) (λ _ → Set ℓ)
  Eq A = _≡_
