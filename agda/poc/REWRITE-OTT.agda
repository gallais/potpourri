{-# OPTIONS --rewriting #-}

module poc.REWRITE-OTT where

data Bool : Set where
  tt ff : Bool

data Nat : Set where
  zero : Nat
  succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}


data Fin : Nat → Set where
  zero : {n : Nat} → Fin (succ n)
  succ : {n : Nat} → Fin n → Fin (succ n)


record ⊤ : Set where
  constructor ⟨⟩

open import Data.Empty
open import Data.Product

Π : (A : Set) (B : A → Set) → Set
Π A B = ∀ a → B a

postulate
  _≅_ : Set → Set → Set
  _≣_ : {A B : Set} → A → B → Set

  Rule : ∀ {ℓ} {A : Set ℓ} → A → A → Set
  

  refl-≅ : {A : Set} → Rule (A ≅ A) ⊤

  fin-≅  : {m n : Nat} → Rule (Fin m ≅ Fin n) (m ≣ n)
  pi-≅   : {A C : Set} {B : A → Set} {D : C → Set} →
           Rule (Π A B ≅ Π C D) (C ≅ A × ∀ c a → c ≣ a → B a ≅ D c)
  sig-≅  : {A C : Set} {B : A → Set} {D : C → Set} →
           Rule (Σ A B ≅ Σ C D) (A ≅ C × ∀ a c → a ≣ c → B a ≅ D c)


  refl-≣ : {A : Set} (a : A) → Rule (a ≣ a) ⊤

  fin-≣ : ∀ {m n} {k : Fin m} {l : Fin n} → Rule (Fin.succ k ≣ Fin.succ l) (k ≣ l)
  nat-≣ : ∀ {m n} → Rule (Nat.succ m ≣ Nat.succ n) (m ≣ n)

  ¬tt≣ff : Rule (tt ≣ ff) ⊥
  ¬ff≣tt : Rule (ff ≣ tt) ⊥
  
  ¬0≣1+n : ∀ {n} → Rule (Nat.zero ≣ Nat.succ n) ⊥
  ¬1+n≣0 : ∀ {n} → Rule (Nat.succ n ≣ Nat.zero) ⊥

  ¬z≣sn  : ∀ {m n} {l : Fin n} → Rule (Fin.zero {m} ≣ Fin.succ l) ⊥
  ¬sn≣z  : ∀ {m n} {k : Fin m} → Rule (Fin.succ k ≣ Fin.zero {n}) ⊥
  

  fun-≣ : {A C : Set} {B : A → Set} {D : C → Set} {f : ∀ a → B a} {g : ∀ c → D c} →
          Rule (f ≣ g) (∀ c a → c ≣ a → f a ≣ g c)
  sig-≣ : {A C : Set} {B : A → Set} {D : C → Set} {p : Σ A B} {q : Σ C D} →
          Rule (p ≣ q) (proj₁ p ≣ proj₁ q × proj₂ p ≣ proj₂ q)


  trans-≣ : {A B C : Set} {a : A} {b : B} {c : C} → a ≣ b → b ≣ c → a ≣ c


{-# BUILTIN REWRITE Rule            #-}
{-# REWRITE pi-≅ refl-≅ sig-≅ fin-≅ #-}
{-# REWRITE refl-≣              #-}
{-# REWRITE ¬tt≣ff ¬ff≣tt       #-}
{-# REWRITE nat-≣ ¬0≣1+n ¬1+n≣0 #-}
{-# REWRITE fin-≣ ¬z≣sn ¬sn≣z   #-}
{-# REWRITE fun-≣ sig-≣         #-}

postulate
  coerce    : (A B : Set) → A ≅ B → A → B
  coherence : (A B : Set) (eq : A ≅ B) (a : A) → a ≣ coerce A B eq a

  coerce-refl : {A : Set} {a : A} (eq : A ≅ A) → Rule (coerce A A eq a) a
  coerce-pi   : {A C : Set} {B : A → Set} {D : C → Set} →
                {eq : Π A B ≅ Π C D} {f : ∀ a → B a} →
                Rule (coerce (∀ a → B a) (∀ c → D c) eq f)
                     (λ c → let a   = coerce C A (proj₁ eq) c
                                c≣a = coherence C A (proj₁ eq) c
                            in coerce (B a) (D c) (proj₂ eq c a c≣a) (f a))
  coerce-sig  : {A C : Set} {B : A → Set} {D : C → Set} →
                {eq : Σ A B ≅ Σ C D} {p : Σ A B} →
                Rule (coerce (Σ A B) (Σ C D) eq p)
                     (let (a , b) = p
                          c       = coerce A C (proj₁ eq) a
                          a≣c     = coherence A C (proj₁ eq) a
                      in (c , coerce (B a) (D c) (proj₂ eq a c a≣c) b))
  coerce-finz : {m n : Nat} {eq : m ≣ n} →
                Rule (coerce (Fin (succ m)) (Fin (succ n)) eq Fin.zero) Fin.zero
  coerce-fins : {m n : Nat} {eq : m ≣ n} {k : Fin m} →
                Rule (coerce (Fin (succ m)) (Fin (succ n)) eq (Fin.succ k))
                     (Fin.succ (coerce (Fin m) (Fin n) eq k))


{-# REWRITE coerce-refl coerce-pi coerce-sig #-}

if : ∀ {ℓ} {A : Set ℓ} → Bool → A → A → A
if tt A B = A
if ff A B = B

open import Function

lemma : (∀ b → if b Nat Nat) ≅ ((b : Bool) → Nat)
lemma = ⟨⟩ , λ { _ tt _ → ⟨⟩ ; _ ff _ → ⟨⟩ }

toNat : Bool → Nat
toNat = coerce (∀ b → if b Nat Nat) (Bool → Nat) lemma $ λ { tt → zero ; ff → succ zero }

vals : (λ b → if b 0 1) ≣ toNat
vals = λ { tt tt _ → ⟨⟩
         ; ff ff _ → ⟨⟩
         ; tt ff ()
         ; ff tt ()
         }

postulate
  _+_    : Nat → Nat → Nat
  +-comm : {m n : Nat} → (m + n) ≣ (n + m)

Vec : Set → Nat → Set
Vec A n = Fin n → A

List : Set → Set
List = Σ Nat ∘ Vec

vecs : {A : Set} {m n : Nat} {a : A} →
       (List A ∋ (m + n , λ _ → a)) ≣ (List A ∋ n + m , λ _ → a)
vecs = +-comm , λ _ _ _ → ⟨⟩
