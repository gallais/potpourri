-- The content of this file is based on:
-- "Finite Sets in Homotopy Type Theory" by
-- Dan Frumin, Herman Geuvers, Léon Gondelman, and Niels van der Weide

{-# OPTIONS --cubical #-}

module fshott18 where

open import Cubical

infixr 6 _∪_
data K (A : Set) : Set where
  ⊘     : K A
  ⟨_⟩   : A → K A
  _∪_   : K A → K A → K A
  nl    : ∀ x → ⊘ ∪ x ≡ x
  nr    : ∀ x → x ∪ ⊘ ≡ x
  idem  : ∀ x → ⟨ x ⟩ ∪ ⟨ x ⟩ ≡ ⟨ x ⟩
  assoc : ∀ x y z → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  comm  : ∀ x y → x ∪ y ≡ y ∪ x
  trunc : ∀ x y → (p q : x ≡ y) → p ≡ q

union-idem : ∀ {A} (x : K A) → x ∪ x ≡ x
union-idem ⊘                   = nl ⊘
union-idem ⟨ x ⟩               = idem x
union-idem (x ∪ y)             = begin
 (x ∪ y) ∪ x ∪ y   ≡⟨ assoc (x ∪ y) x y ⟩
 ((x ∪ y) ∪ x) ∪ y ≡⟨ cong (λ s → (s ∪ x) ∪ y) (comm x y) ⟩
 ((y ∪ x) ∪ x) ∪ y ≡⟨ cong (_∪ y) (sym (assoc y x x)) ⟩
 (y ∪ x ∪ x) ∪ y   ≡⟨ cong (λ s → (y ∪ s) ∪ y) (union-idem x) ⟩
 (y ∪ x) ∪ y       ≡⟨ cong (_∪ y) (comm y x) ⟩
 (x ∪ y) ∪ y       ≡⟨ sym (assoc x y y) ⟩
 x ∪ y ∪ y         ≡⟨ cong (x ∪_) (union-idem y) ⟩
 x ∪ y             ∎
union-idem (nl x i)            = {!!}
union-idem (nr x i)            = {!!}
union-idem (idem x i)          = {!!}
union-idem (assoc x y z i)     = {!!}
union-idem (comm x y i)        = {!!}
union-idem (trunc x y p q i j) = {!!}
