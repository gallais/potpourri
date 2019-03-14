-- The content of this file is based on:
-- "Finite Sets in Homotopy Type Theory" by
-- Dan Frumin, Herman Geuvers, Léon Gondelman, and Niels van der Weide

{-# OPTIONS --safe --cubical #-}

module fshott18 where

open import Cubical.Core.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

infixr 6 _∪_
data K {a} (A : Set a) : Set a where
  ∅     : K A
  ⟨_⟩   : A → K A
  _∪_   : K A → K A → K A
  Knl    : (x : K A) → ∅ ∪ x ≡ x
  Knr    : (x : K A) → x ∪ ∅ ≡ x
  Kidem  : (x : A) → ⟨ x ⟩ ∪ ⟨ x ⟩ ≡ ⟨ x ⟩
  Kassoc : (x y z : K A) → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  Kcomm  : (x y : K A) → x ∪ y ≡ y ∪ x
  Ktrunc : ∀ (x y : K A) (p q : x ≡ y) → p ≡ q

private
  variable
    a b : Level
    A : Set a
    B : Set b

isProp-isSet : isProp A → isSet A
isProp-isSet A-prop = Discrete→isSet λ x y → yes (A-prop x y)

isProp-isSetP : ∀ {p} {P : A → Set p} →
  (∀ k → isProp (P k)) →
  ∀ {k l : A} (p : k ≡ l) (pk : P k) (pl : P l) →
  (v w : PathP (λ j → P (p j)) pk pl) →
  v ≡ w
isProp-isSetP {P = P} pr {k} p pk pl v w =
  J (λ m (eq : k ≡ m) → ∀ (pm : P m) (v w : PathP (λ j → P (eq j)) pk pm) → v ≡ w)
   (isProp-isSet (pr _) _)
   p
   pl
   v w

module _ {p} {P : Set p} (pr : isProp P)
         (n : P) (s : A → P) (u : P → P → P) where

  K-recᴾ : K A → P
  K-recᴾ ∅                    = n
  K-recᴾ ⟨ a ⟩                = s a
  K-recᴾ (k ∪ l)              = u (K-recᴾ k) (K-recᴾ l)
  K-recᴾ (Knl k i)            = pr (u n (K-recᴾ k)) (K-recᴾ k) i
  K-recᴾ (Knr k i)            = pr (u (K-recᴾ k) n) (K-recᴾ k) i
  K-recᴾ (Kidem k i)          = pr (u (s k) (s k)) (s k) i
  K-recᴾ (Kassoc k l m i)     = pr (u (K-recᴾ k) (u (K-recᴾ l) (K-recᴾ m)))
                                   (u (u (K-recᴾ k) (K-recᴾ l)) (K-recᴾ m)) i
  K-recᴾ (Kcomm k l i)        = pr (u (K-recᴾ k) (K-recᴾ l))
                                   (u (K-recᴾ l) (K-recᴾ k)) i
  K-recᴾ (Ktrunc k l p q i j) =
    isProp-isSet pr (K-recᴾ k) (K-recᴾ l)
                    (λ i → K-recᴾ (p i)) (λ i → K-recᴾ (q i))
                    i j

module _ {p} {P : K A → Set p}
         (pr' : ∀ k → isProp (P k))
         (n : P ∅) (s : (a : A) → P ⟨ a ⟩)
         (u : ∀ {k l} → P k → P l → P (k ∪ l)) where

  private
    pr : ∀ {k l} (eq : k ≡ l) (p : P k) (q : P l) → PathP (λ i → P (eq i)) p q
    pr = J (λ k eq → ∀ p q → PathP (λ i → P (eq i)) p q) (pr' _)

    PR : ∀ {k l} (p q : k ≡ l) (pk : P k) (pl : P l)
         (v : PathP (λ j → P (p j)) pk pl) →
         (w : PathP (λ j → P (q j)) pk pl) →
         (eq : p ≡ q) → PathP (λ i → PathP (λ j → P (eq i j)) pk pl) v w
    PR p q pk pl v w eq =
      J (λ pq (eq : p ≡ pq) →
                  ∀ (v : PathP (λ j → P (eq i0 j)) pk pl)
                    (w : PathP (λ j → P (eq i1 j)) pk pl) →
                  PathP (λ i → PathP (λ j → P (eq i j)) pk pl) v w)
          (isProp-isSetP pr' p pk pl)
          eq
          v w


  K-elimᴾ : ∀ a → P a
  K-elimᴾ ∅                    = n
  K-elimᴾ ⟨ a ⟩                = s a
  K-elimᴾ (k ∪ l)              = u (K-elimᴾ k) (K-elimᴾ l)
  K-elimᴾ (Knl k i)            = pr (Knl k) (u n (K-elimᴾ k)) (K-elimᴾ k) i
  K-elimᴾ (Knr k i)            = pr (Knr k) (u (K-elimᴾ k) n) (K-elimᴾ k) i
  K-elimᴾ (Kidem k i)          = pr (Kidem k) (u (s k) (s k)) (s k) i
  K-elimᴾ (Kassoc k l m i)     =
    pr (Kassoc k l m) (u (K-elimᴾ k) (u (K-elimᴾ l) (K-elimᴾ m)))
                      (u (u (K-elimᴾ k) (K-elimᴾ l)) (K-elimᴾ m)) i
  K-elimᴾ (Kcomm k l i)        =
    pr (Kcomm k l) (u (K-elimᴾ k) (K-elimᴾ l))
                   (u (K-elimᴾ l) (K-elimᴾ k)) i
  K-elimᴾ (Ktrunc k l p q i j) =
    PR p q (K-elimᴾ k) (K-elimᴾ l)
           (λ j → K-elimᴾ (p j)) (λ j → K-elimᴾ (q j))
           (Ktrunc k l p q)
           i j

KisSet : isSet (K A)
KisSet = Ktrunc

_IdempotentOn_ : ∀ {a} {A : Set a} → (A → A → A) → A → Set a
f IdempotentOn a = f a a ≡ a

idem-∪ : ∀ (x y : K A) →
  _∪_ IdempotentOn x →
  _∪_ IdempotentOn y →
  _∪_ IdempotentOn (x ∪ y)
idem-∪ x y idem-x idem-y =
   (x ∪ y) ∪ x ∪ y   ≡⟨ Kassoc (x ∪ y) x y ⟩
   ((x ∪ y) ∪ x) ∪ y ≡⟨ cong (λ s → (s ∪ x) ∪ y) (Kcomm x y) ⟩
   ((y ∪ x) ∪ x) ∪ y ≡⟨ cong (_∪ y) (sym (Kassoc y x x)) ⟩
   (y ∪ x ∪ x) ∪ y   ≡⟨ cong (λ s → (y ∪ s) ∪ y) idem-x ⟩
   (y ∪ x) ∪ y       ≡⟨ cong (_∪ y) (Kcomm y x) ⟩
   (x ∪ y) ∪ y       ≡⟨ sym (Kassoc x y y) ⟩
   x ∪ y ∪ y         ≡⟨ cong (x ∪_) idem-y ⟩
   x ∪ y             ∎

idem-isProp : isSet (K A)
idem-isProp p q = Ktrunc _ _

-- Lemma 2.3
idem : (k : K A) → _∪_ IdempotentOn k
idem = K-elimᴾ (λ k → KisSet (k ∪ k) k) (Knl ∅) Kidem (idem-∪ _ _)

data Squashed {a} (A : Set a) : Set a where
  elt   : A → Squashed A
  trunc : ∀ (x y : Squashed A) → x ≡ y

Squashed-isSet : isSet (Squashed A)
Squashed-isSet = Discrete→isSet (λ x y → yes (trunc x y))

open import Level using (Lift)
open import Data.Empty
open import Data.Sum.Base

open import Cubical.Core.Glue

⊎-comm : (A ⊎ B) ≡ (B ⊎ A)
⊎-comm = ua (to , prf) where

  to : A ⊎ B → B ⊎ A
  to (inj₁ a) = inj₂ a
  to (inj₂ b) = inj₁ b

  to² : ∀ (x : A ⊎ B) → to (to x) ≡ x
  to² (inj₁ a) = refl
  to² (inj₂ b) = refl

  prf : isEquiv to
  prf .equiv-proof y .fst               = to y , to² y
  prf .equiv-proof y .snd (inj₁ a , eq) =
    J (λ y eq → (to y , to² y) ≡ (_ , eq)) refl eq
  prf .equiv-proof y .snd (inj₂ b , eq) =
    J (λ y eq → (to y , to² y) ≡ (_ , eq)) refl eq

open import Function

⊎-idˡ : ∀ {a} {A : Set a} → (Lift a ⊥ ⊎ A) ≡ A
⊎-idˡ {a} {A} = ua (to , prf) where

  to : Lift a ⊥ ⊎ A → A
  to (inj₂ a) = a

  prf : isEquiv to
  prf .equiv-proof a .fst               = inj₂ a , refl
  prf .equiv-proof a .snd (inj₂ b , eq) =
    J (λ y eq → (inj₂ y , _) ≡ (fiber to y ∋ _ , eq)) refl eq

⊎-idʳ : ∀ {a} {A : Set a} → (A ⊎ Lift a ⊥) ≡ A
⊎-idʳ = ⊎-comm ∙ ⊎-idˡ

open import Cubical.Foundations.HLevels

Squashed-id : isProp A → Squashed A ≡ A
Squashed-id {A = A} pr = ua (to , prf) where

  to : Squashed A → A
  to (elt a)       = a
  to (trunc a b i) = pr (to a) (to b) i

  prf : isEquiv to
  prf .equiv-proof a =
    isContrSigma (elt a , trunc _) λ x →
      inhProp→isContr (pr (to x) a) (isProp→isSet pr (to x) a)

infixr 6 _+_
_+_ : Set a → Set b → Set _
A + B = Squashed (A ⊎ B)

+-comm : A + B ≡ B + A
+-comm = cong Squashed ⊎-comm

+-idˡ : isProp {a} A → Lift a ⊥ + A ≡ A
+-idˡ pr = cong Squashed ⊎-idˡ ∙ Squashed-id pr

+-idʳ : isProp {a} A → A + Lift a ⊥ ≡ A
+-idʳ pr = +-comm ∙ +-idˡ pr

-- Definition 2.4
_∈_ : A → K A → Set _
a ∈ ∅                  = Lift _ ⊥
a ∈ ⟨ b ⟩              = Squashed (a ≡ b)
a ∈ (k ∪ l)            = a ∈ k + a ∈ l
a ∈ Knl k i            = {!!}
a ∈ Knr k i            = {!!}
a ∈ Kidem x i          = {!!}
a ∈ Kassoc k l m i     = {!!}
a ∈ Kcomm k l i        = {!!}
a ∈ Ktrunc k l p q i j = {!!}

{-
open import Cubical
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

data ∥_∥ (A : Set) : Set where
  elt   : A → ∥ A ∥
  trunc : ∀ x y → elt x ≡ elt y

_∨_ : (A B : Set) → Set
A ∨ B = ∥ A ⊎ B ∥

_∧_ : (A B : Set) → Set
A ∧ B = ∥ A × B ∥

module _ {A B : Set} where

  ∨-comm : A ∨ B → B ∨ A
  ∨-comm (elt (inj₁ a)) = elt (inj₂ a)
  ∨-comm (elt (inj₂ b)) = elt (inj₁ b)
  ∨-comm (trunc (inj₁ a₁) (inj₁ a₂) i) = trunc (inj₂ a₁) (inj₂ a₂) i
  ∨-comm (trunc (inj₁ a₁) (inj₂ b₂) i) = trunc (inj₂ a₁) (inj₁ b₂) i
  ∨-comm (trunc (inj₂ b₁) (inj₁ a₂) i) = trunc (inj₁ b₁) (inj₂ a₂) i
  ∨-comm (trunc (inj₂ b₁) (inj₂ b₂) i) = trunc (inj₁ b₁) (inj₁ b₂) i

  ∧-comm : A ∧ B → B ∧ A
  ∧-comm (elt (a , b))                 = elt (b , a)
  ∧-comm (trunc (a₁ , b₁) (a₂ , b₂) i) = trunc (b₁ , a₁) (b₂ , a₂) i

  ∧-× : A ∧ B → ∥ A ∥ × ∥ B ∥
  ∧-× (elt (a , b))                 = elt a , elt b
  ∧-× (trunc (a₁ , b₁) (a₂ , b₂) i) = trunc a₁ a₂ i , trunc b₁ b₂ i

infixr 6 _∪_
data K (A : Set) : Set where
  ⊘     : K A
  ⟨_⟩   : A → K A
  _∪_   : K A → K A → K A
  Knl    : ∀ x → ⊘ ∪ x ≡ x
  Knr    : ∀ x → x ∪ ⊘ ≡ x
  Kidem  : ∀ x → ⟨ x ⟩ ∪ ⟨ x ⟩ ≡ ⟨ x ⟩
  Kassoc : ∀ x y z → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  Kcomm  : ∀ x y → x ∪ y ≡ y ∪ x
  Ktrunc : ∀ x y (p q : x ≡ y) → p ≡ q

infixr 6 _∷_
data L (A : Set) : Set where
  []    : L A
  _∷_   : A → L A → L A
  Ldupl  : ∀ x xs → x ∷ x ∷ xs ≡ x ∷ xs
  Lcomm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  Ltrunc : ∀ x y (p q : x ≡ y) → p ≡ q

module _ {A : Set} where

  union-idem : (x : K A) → x ∪ x ≡ x
  union-idem ⊘                     = Knl ⊘
  union-idem ⟨ x ⟩                = Kidem x
  union-idem (x ∪ y)              = begin
   (x ∪ y) ∪ x ∪ y   ≡⟨ Kassoc (x ∪ y) x y ⟩
   ((x ∪ y) ∪ x) ∪ y ≡⟨ cong (λ s → (s ∪ x) ∪ y) (Kcomm x y) ⟩
   ((y ∪ x) ∪ x) ∪ y ≡⟨ cong (_∪ y) (sym (Kassoc y x x)) ⟩
   (y ∪ x ∪ x) ∪ y   ≡⟨ cong (λ s → (y ∪ s) ∪ y) (union-idem x) ⟩
   (y ∪ x) ∪ y       ≡⟨ cong (_∪ y) (Kcomm y x) ⟩
   (x ∪ y) ∪ y       ≡⟨ sym (Kassoc x y y) ⟩
   x ∪ y ∪ y         ≡⟨ cong (x ∪_) (union-idem y) ⟩
   x ∪ y             ∎
  union-idem (Knl x i)            = {!!}
  union-idem (Knr x i)            = {!!}
  union-idem (Kidem x i)          = {!!}
  union-idem (Kassoc x y z i)     = {!!}
  union-idem (Kcomm x y i)        = {!!}
  union-idem (Ktrunc x y p q i j) = {!!}

{-
  _∈_ : (a : A) → K A → Set
  a ∈ ⊘                 = ⊥
  a ∈ ⟨ x ⟩             = ∥ a ≡ x ∥
  a ∈ (x ∪ y)           = {!!}
  a ∈ nl x i            = {!!}
  a ∈ nr x i            = {!!}
  a ∈ idem x i          = {!!}
  a ∈ assoc x y z i     = {!!}
  a ∈ comm x y i        = {!!}
  a ∈ trunc x y p q i j = {!!}
-}
