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
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

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


JisProp : ∀ {p} {P : A → Set p} → (∀ a → isProp (P a)) →
          ∀ {a b} (eq : a ≡ b) (p : P a) (q : P b) → PathP (λ i → P (eq i)) p q
JisProp {P = P} pr = J (λ k eq → ∀ p q → PathP (λ i → P (eq i)) p q) (pr _)

module _ {p} {P : K A → Set p}
         (pr' : ∀ k → isProp (P k))
         (n : P ∅) (s : (a : A) → P ⟨ a ⟩)
         (u : ∀ {k l} → P k → P l → P (k ∪ l)) where

  private

    pr = JisProp pr'

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


module _ {p} {P : Squashed A → Set p}
         (pr : ∀ a → isProp (P a))
         (pa : ∀ a → P (elt a)) where

  private

    pr' : ∀ {k l} (eq : k ≡ l) (p : P k) (q : P l) → PathP (λ i → P (eq i)) p q
    pr' = J (λ k eq → ∀ p q → PathP (λ i → P (eq i)) p q) (pr _)

  Squashed-elimᴾ : ∀ a → P a
  Squashed-elimᴾ (elt a)       = pa a
  Squashed-elimᴾ (trunc a b i) = pr' (trunc a b) (Squashed-elimᴾ a) (Squashed-elimᴾ b) i


Squashed-isProp : isProp (Squashed A)
Squashed-isProp = trunc

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

⊎-assoc : (A ⊎ (B ⊎ C)) ≡ ((A ⊎ B) ⊎ C)
⊎-assoc {A = A} {B = B} {C = C} = ua (to , prf) where

  to : A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
  to (inj₁ a)        = inj₁ (inj₁ a)
  to (inj₂ (inj₁ b)) = inj₁ (inj₂ b)
  to (inj₂ (inj₂ c)) = inj₂ c

  from : (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
  from (inj₁ (inj₁ a)) = inj₁ a
  from (inj₁ (inj₂ b)) = inj₂ (inj₁ b)
  from (inj₂ c)        = inj₂ (inj₂ c)

  to-from : ∀ a → to (from a) ≡ a
  to-from (inj₁ (inj₁ a)) = refl
  to-from (inj₁ (inj₂ b)) = refl
  to-from (inj₂ c)        = refl

  to-from-id : ∀ b → (from (to b) , to-from (to b))
                   ≡ (fiber to (to b) ∋ b , refl)
  to-from-id (inj₁ a)        = refl
  to-from-id (inj₂ (inj₁ b)) = refl
  to-from-id (inj₂ (inj₂ c)) = refl

  prf : isEquiv to
  prf .equiv-proof a .fst          = from a , to-from a
  prf .equiv-proof a .snd (b , eq) =
    J (λ a eq → (from a , to-from a) ≡ (b , eq)) (to-from-id b) eq

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
  to = Squashed-elimᴾ (const pr) id

  prf : isEquiv to
  prf .equiv-proof a =
    isContrSigma (elt a , trunc _) λ x →
      inhProp→isContr (pr (to x) a) (isProp→isSet pr (to x) a)

infixr 6 _+_
_+_ : Set a → Set b → Set _
A + B = Squashed (A ⊎ B)

+-comm : ∀ {a b} (A : Set a) (B : Set b) → A + B ≡ B + A
+-comm A B = cong Squashed ⊎-comm

+-squashedʳ : A + Squashed B ≡ A + B
+-squashedʳ {A = A} {B = B} = ua (to , prf) where

  to : A + Squashed B → A + B
  to = Squashed-elimᴾ (const Squashed-isProp)
     [ elt ∘′ inj₁
     , Squashed-elimᴾ (const Squashed-isProp) (elt ∘′ inj₂)
     ]′

  from : A + B → A + Squashed B
  from = Squashed-elimᴾ (const Squashed-isProp)
       [ elt ∘′ inj₁
       , elt ∘′ inj₂ ∘′ elt
       ]′

  prf : isEquiv to
  prf .equiv-proof a = isContrSigma (from a , trunc _) λ x →
    inhProp→isContr (Squashed-isProp (to x) a)
                    (isProp→isSet Squashed-isProp (to x) a)

+-squashedˡ : Squashed A + B ≡ A + B
+-squashedˡ {A = A} {B = B} =
  Squashed A + B ≡⟨ +-comm _ _ ⟩
  B + Squashed A ≡⟨ +-squashedʳ ⟩
  B + A          ≡⟨ +-comm _ _ ⟩
  A + B          ∎

+-assoc : ∀ {a b c} (A : Set a) (B : Set b) (C : Set c) →
          A + (B + C) ≡ (A + B) + C
+-assoc A B C =
  A + B + C              ≡⟨ +-squashedʳ ⟩
  Squashed (A ⊎ B ⊎ C)   ≡⟨ cong Squashed ⊎-assoc ⟩
  Squashed ((A ⊎ B) ⊎ C) ≡⟨ sym +-squashedˡ ⟩
  (A + B) + C            ∎

+-idˡ : isProp {a} A → Lift a ⊥ + A ≡ A
+-idˡ pr = cong Squashed ⊎-idˡ ∙ Squashed-id pr

+-idʳ : isProp {a} A → A + Lift a ⊥ ≡ A
+-idʳ pr = +-comm _ _ ∙ +-idˡ pr

+-idem : ∀ {a} (A : Set a) → isProp A → A + A ≡ A
+-idem A pr = ua (to , prf) where

  to : A + A → A
  to (elt a)       = [ id , id ]′ a
  to (trunc a b i) = pr (to a) (to b) i

  prf : isEquiv to
  prf .equiv-proof a = isContrSigma (elt (inj₁ a) , trunc _) λ x →
    inhProp→isContr (pr (to x) a) (isProp→isSet pr (to x) a)

open import Cubical.Foundations.Univalence as U using (univalencePath)
open import Cubical.Foundations.Equiv

{-

h : ∀ {ℓ} (A B : hProp {ℓ}) → fst A ≡ fst B → A ≡ B
h A B eq =
  J (λ s eq → ∀ (t : isProp s) → (s , t) ≡ B)
     (λ t i → (_ , isPropIsProp t (snd B) i))
     (sym eq)
     (snd A)

-}

module _ {p} {P : A → Set p} where

  dcong : ∀ (f : ∀ a → P a) {a a′} (p : a ≡ a′) →
          PathP (λ i → P (p i)) (f a) (f a′)
  dcong f p i = f (p i)

module _ {p} {P : A → Set p} where

  Σ-unfold : (p q : Σ A P) → Set _
  Σ-unfold p q = Σ[ eq ∈ fst p ≡ fst q ]
                    PathP (λ i → P (eq i)) (snd p) (snd q)

  unfold : ∀ p q → (p ≡ q) ≃ (Σ-unfold p q)
  unfold p q = isoToEquiv (iso to from to-from from-to) where

    to : p ≡ q → Σ-unfold p q
    to eq = cong fst eq , dcong snd eq

    from : Σ-unfold p q → p ≡ q
    from (f , s) i = f i , s i

    to-from : section to from
    to-from (f , s) = refl

    from-to : retract to from
    from-to eq = refl

  Σ-Prop : (pr : ∀ a → isContr (P a)) → Σ A P ≃ A
  Σ-Prop kr = isoToEquiv (iso to from to-from from-to) where

    to : Σ A P → A
    to = fst

    from : A → Σ A P
    from a = a , fst (kr a)

    to-from : section to from
    to-from b = refl

    from-to : retract to from
    from-to a i = fst a , snd (kr (fst a)) (snd a) i

i : ∀ {p} {P : A → Set p} (pr : ∀ a → isProp (P a)) →
    (p q : Σ A P) → (fst p ≡ fst q) ≃ (p ≡ q)
i {P = P} pr p q = compEquiv (invEquiv (Σ-Prop contr))(invEquiv (unfold p q))

  where

  contr : (a : fst p ≡ fst q) → isContr (PathP (λ i → P (a i)) (snd p) (snd q))
  contr a = inhProp→isContr (JisProp pr a (snd p) (snd q))
                            (isProp-isSetP pr a (snd p) (snd q))


h : ∀ {ℓ} (A B : hProp {ℓ}) → (fst A ≡ fst B) ≃ (A ≡ B)
h = i (λ a → isPropIsProp)

weqeqmap : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A ≡ B
weqeqmap f = subst id (sym univalencePath) (U.lift f)

hProp-isSet : ∀ {ℓ} → isSet (hProp {ℓ})
hProp-isSet A@(s , prs) B@(t , prt) =
  subst isProp (weqeqmap (h A B)) g

   where

   d : isProp (s → t)
   d f g i a = prt (f a) (g a) i

   e : isProp (s ≃ t)
   e (f , prf) (g , prg) = equivEq (f , prf) (g , prg) (d f g)

   f : isProp (U.Lift (s ≃ t))
   f = λ x y → cong U.lift (e (U.lower x) (U.lower y))

   g : isProp (s ≡ t)
   g = subst isProp (sym U.univalencePath) f

-- Definition 2.4
_∈_ : A → K A → hProp
a ∈ ∅                  = Lift _ ⊥ , λ ()
a ∈ ⟨ b ⟩              = Squashed (a ≡ b)
                       , Squashed-isProp
a ∈ (k ∪ l)            = fst (a ∈ k) + fst (a ∈ l)
                       , Squashed-isProp
a ∈ Knl k i            =
  J (λ s eq → ∀ t → (s , t) ≡ (a ∈ k))
    (λ t i → _ , isPropIsProp t (snd (a ∈ k)) i)
    (sym (+-idˡ (snd (a ∈ k))))
    Squashed-isProp
    i
a ∈ Knr k i            =
  J (λ s eq → ∀ t → (s , t) ≡ (a ∈ k))
    (λ t i → _ , isPropIsProp t (snd (a ∈ k)) i)
    (sym (+-idʳ (snd (a ∈ k))))
    Squashed-isProp
    i
a ∈ Kidem b i          =
  J (λ s eq → ∀ (t : isProp s) → (s , t) ≡ (Squashed (a ≡ b) , Squashed-isProp))
     (λ t i → _ , isPropIsProp t Squashed-isProp i)
     (sym (+-idem (Squashed (a ≡ b)) Squashed-isProp))
     Squashed-isProp
     i
a ∈ Kassoc k l m i     =
  let A = fst (a ∈ k); B = fst (a ∈ l); C = fst (a ∈ m) in
  J (λ s eq → ∀ (t : isProp s) → (s , t) ≡ ((A + B) +  C , Squashed-isProp))
     (λ t i → _ , isPropIsProp t Squashed-isProp i)
     (sym (+-assoc A B C))
     Squashed-isProp
     i
a ∈ Kcomm k l i        =
  let A = fst (a ∈ k); B = fst (a ∈ l) in
  J (λ s eq → ∀ (t : isProp s) → (s , t) ≡ (B + A , Squashed-isProp))
     (λ t i → _ , isPropIsProp t Squashed-isProp i)
     (sym (+-comm A B))
     Squashed-isProp
     i
a ∈ Ktrunc k l p q i j =
  hProp-isSet (a ∈ k) (a ∈ l) (λ i → a ∈ p i) (λ i → a ∈ q i) i j

{-
infixr 6 _∷_
data L (A : Set) : Set where
  []    : L A
  _∷_   : A → L A → L A
  Ldupl  : ∀ x xs → x ∷ x ∷ xs ≡ x ∷ xs
  Lcomm  : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  Ltrunc : ∀ x y (p q : x ≡ y) → p ≡ q
-}
