-- The content of this file is based on Dylus, Christiansen and Teegen's
-- One Monad To Prove Them All
-- (Programming, 2019)

module papers.dct19.OneMonadToProveThemAll.Container where

open import Level
open import Size
open import Data.Empty
open import Data.Unit
open import Data.Sum as Sum using (inj₁; inj₂)
open import Data.Product as Prod
open import Function using (_∘′_)

open import Data.Container
open import Data.Container.Combinator
open import Relation.Binary.PropositionalEquality as P using (_≡_)

data _⋆_ {s p a} (C : Container s p) (A : Set a) : Set (s ⊔ p ⊔ a) where
  pure   : A → C ⋆ A
  impure : ⟦ C ⟧ (C ⋆ A) → C ⋆ A

nothing : ∀ {a} {A : Set a} → const {p = zero} ⊤ ⋆ A
nothing = impure (_ , λ ())

open import Category.Functor

module _ {s p} {C : Container s p}
         {a b} {A : Set a} {B : Set b} (pur : A → B) (ipur : ⟦ C ⟧ B → B)
         where

  foldFree : C ⋆ A → B
  foldFree (pure a)         = pur a
  foldFree (impure (e , f)) = ipur (e , λ p → foldFree (f p))

module _ {s p} {C : Container s p}
         {a b} {A : Set a} {B : Set b}
         where

  _>>=_ : C ⋆ A → (A → C ⋆ B) → C ⋆ B
  ma >>= f = foldFree f impure ma

data List {s p a} (C : Container s p) (A : Set a) : Size → Set (a ⊔ s ⊔ p) where
  []  : ∀ {i} → List C A i
  _∷_ : ∀ {i} → C ⋆ A → C ⋆ (List C A i) → List C A (↑ i)

pattern []ᵉ       = pure []
pattern _∷ᵉ_ x xs = pure (x ∷ xs)

module _ {s p a} {C : Container s p} {A : Set a} where

  _++_ : ∀ {i} → C ⋆ List C A i → C ⋆ List C A _ → C ⋆ List C A _
  xs ++ ys = xs >>= λ where
    []       → ys
    (x ∷ xs) → x ∷ᵉ (xs ++ ys)

  ++-assoc : ∀ {i} (xs : C ⋆ List C A i) ys zs →
             (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc []ᵉ              ys zs = P.refl
  ++-assoc (x ∷ᵉ xs)        ys zs = P.cong (x ∷ᵉ_) (++-assoc xs ys zs)
  ++-assoc (impure (e , f)) ys zs =
    P.cong (impure ∘′ (e ,_)) {!!}
