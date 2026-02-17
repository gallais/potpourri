{-# OPTIONS --guardedness #-}

module Resumption where

open import Algebra.Definitions.RawMagma
open import Relation.Binary.Bundles using (Preorder)

module Definition {a r e} (P : Preorder a e r) where

  open Preorder P
    renaming (Carrier to A)

  open import Level using (Level; _⊔_)
  open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

  open import Algebra.Bundles using (Monoid)

  open import Relation.Unary.Closure.Base _≲_

  data Res {b} (B : A → Set b) (x : A) : Set (a ⊔ r ⊔ b)

  record Thunk {b} (B : A → Set b) (x : A)  : Set (a ⊔ r ⊔ b) where
    coinductive
    field force : □ (Res B) x
  open Thunk public

  data Res B x where
    completed : B x → Res B x
    suspended : Thunk B x → Res B x



module Example where

  open import Data.List.Base using (List; []; _∷_)
  open import Data.List.Properties using (++-monoid)
  open import Data.Nat.Base using (ℕ)

  open import Algebra.Properties.Monoid.Divisibility (++-monoid ℕ)

  open Definition ∣-preorder









{-
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum.Relation.Binary.LeftOrder

data _≤ʳ_ {A : Set a} {B : Set b} : Rel (Comp A B ⊎ B) (a ⊔ b)

_≤ᶜ_ : {A : Set a} {B : Set b} → Rel (Comp A B) (a ⊔ b)
f ≤ᶜ g = ∀ x → call f x ≤ʳ call g x

open import Function.Base using (const)

data _≤ʳ_ where
  inj₁  : ∀ f g → f ≤ᶜ g                     → inj₁ f ≤ʳ inj₁ g
  inj₁₂ : ∀ f b → f ≤ᶜ mkComp (λ _ → inj₂ b) → inj₁ f ≤ʳ inj₂ b
  inj₂  : ∀ b c → b ≡ c                      → inj₂ b ≤ʳ inj₂ c


record RFun {c e b} (A : Monoid c e) (B : Set b) : Set (c ⊔ e ⊔ b) where
  constructor mkRFun
  open Monoid A
  field
    computation : Comp Carrier B
    converging  : ∀ (x e : Carrier) →
      call computation x ≤ʳ call computation (x ∙ e)


open import Data.Nat.Base using (ℕ; zero; suc; _+_)
-}
