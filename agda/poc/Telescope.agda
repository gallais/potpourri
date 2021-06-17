module poc.Telescope where

import Level
open import Data.Nat.Base
open import Data.Product
open import Data.Unit.Polymorphic.Base
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

  open import Agda.Builtin.Equality

  Eq : ∀ {ℓ} → Tele 3 (EqSets ℓ) → Set ℓ
  Eq (((_ , A) , x) , y) = x ≡ y

module Right where

  Sets : ∀ n (ls : Levels n) → Set (Level.suc (⨆ n ls))
  Tele : ∀ n {ls} → Sets n ls → Set (⨆ n ls)

  Sets zero    ls       = ⊤
  Sets (suc n) (l , ls) = Σ[ A ∈ Set l ] (A → Sets n ls)

  Tele zero    _       = ⊤
  Tele (suc n) (A , Γ) = Σ[ a ∈ A ] (Tele n (Γ a))

  open import Function.Base using (_∘_)

  EqSets : ∀ ℓ → Sets 3 _
  EqSets ℓ = Set ℓ , λ A → A , λ _ → A , _

  open import Agda.Builtin.Equality

  Eq : ∀ {ℓ} → Tele 3 (EqSets ℓ) → Set ℓ
  Eq (A , x , y , _) = x ≡ y
