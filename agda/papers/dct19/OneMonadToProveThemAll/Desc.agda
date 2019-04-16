-- The content of this file is based on Dylus, Christiansen and Teegen's
-- One Monad To Prove Them All
-- (Programming, 2019)

module papers.dct19.OneMonadToProveThemAll.Desc where

open import Level
open import Size
open import Data.Empty
open import Data.Unit
open import Data.Sum as Sum
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality as P using (_≡_)

data Desc a : Set (suc a) where
  I   : Desc a
  O Z : Desc a
  K   : Set a → Desc a
  _+_ : Desc a → Desc a → Desc a
  _*_ : Desc a → Desc a → Desc a

⟦_⟧ : ∀ {a} → Desc a → Set a → Set a
⟦ I     ⟧ x = x
⟦ O     ⟧ x = Lift _ ⊤
⟦ Z     ⟧ x = Lift _ ⊥
⟦ K A   ⟧ x = A
⟦ d + e ⟧ x = ⟦ d ⟧ x ⊎ ⟦ e ⟧ x
⟦ d * e ⟧ x = ⟦ d ⟧ x × ⟦ e ⟧ x

module _ {a} {A B : Set a} where

  fmap : (d : Desc a) → (A → B) → ⟦ d ⟧ A → ⟦ d ⟧ B
  fmap I       f v = f v
  fmap Z       f v = v
  fmap O       f v = v
  fmap (K A)   f v = v
  fmap (d + e) f v = Sum.map (fmap d f) (fmap e f) v
  fmap (d * e) f v = Prod.map (fmap d f) (fmap e f) v

  fmap-ext : ∀ d {f g} → (∀ a → f a ≡ g a) → ∀ v → fmap d f v ≡ fmap d g v
  fmap-ext I       ext v        = ext v
  fmap-ext O       ext v        = P.refl
  fmap-ext (K A)   ext v        = P.refl
  fmap-ext (d + e) ext (inj₁ x) = P.cong inj₁ (fmap-ext d ext x)
  fmap-ext (d + e) ext (inj₂ y) = P.cong inj₂ (fmap-ext e ext y)
  fmap-ext (d * e) ext (x , y)  = P.cong₂ _,_ (fmap-ext d ext x) (fmap-ext e ext y)


data μ {a} (d : Desc a) : Size → Set a where
  con : ∀ {i} → ⟦ d ⟧ (μ d i) → μ d (↑ i)

data _⋆_⊣_ {a} (d : Desc a) (A : Set a) : Size → Set a where
  pure   : ∀ {i} → A → d ⋆ A ⊣ (↑ i)
  impure : ∀ {i} → ⟦ d ⟧ (d ⋆ A ⊣ i) → d ⋆ A ⊣ (↑ i)

_⊢_⋆_ : ∀ i {a} (d : Desc a) → Set a → Set a
i ⊢ d ⋆ A = d ⋆ A ⊣ i

module _ {a} {d : Desc a} {A B : Set a} (pur : A → B) (ipur : ⟦ d ⟧ B → B) where

  foldFree : ∀ {i} → i ⊢ d ⋆ A → B
  foldFree (pure a)   = pur a
  foldFree (impure t) = ipur (fmap d foldFree t)

module _ {a} {d : Desc a} {A B : Set a} where

  _>>=_ : ∀ {i} → i ⊢ d ⋆ A → (A → _ ⊢ d ⋆ B) → _ ⊢ d ⋆ B
  ma >>= f = foldFree f impure ma

data List {a} (C : Desc a) (A : Set a) : Size → Set a where
  []  : ∀ {i} → List C A i
  _∷_ : ∀ {i} → _ ⊢ C ⋆ A → _ ⊢ C ⋆ (List C A i) → List C A (↑ i)

pattern []ᵉ       = pure []
pattern _∷ᵉ_ x xs = pure (x ∷ xs)

module _ {a} {d : Desc a} {A : Set a} where

  _++_ : ∀ {i} → _ ⊢ d ⋆ List d A i → _ ⊢ d ⋆ List d A _ → _ ⊢ d ⋆ List d A _
  xs ++ ys = xs >>= λ where
    []       → ys
    (x ∷ xs) → x ∷ᵉ (xs ++ ys)

  ++-assoc : ∀ {i} (xs : _ ⊢ d ⋆ List d A i) ys zs →
             (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc = {!!}
