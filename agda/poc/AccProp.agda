{-# OPTIONS --prop #-}

open import Agda.Builtin.Nat using (Nat; zero; suc)

data _<_ : (m n : Nat) → Prop where
  z<n : ∀ {n} → zero < suc n
  s<s : ∀ {m n} → m < n → suc m < suc n

data Acc (n : Nat) : Set where
  Tick : (∀ m → m < n → Acc m) → Acc n

lemma : ∀ {m n p} → p < suc m → suc m < suc n → p < n
lemma z<n       (s<s z<n)       = z<n
lemma z<n       (s<s (s<s m<n)) = z<n
lemma (s<s z<n) (s<s (s<s m<n)) = s<s (lemma z<n (s<s m<n))
lemma (s<s (s<s p<n)) (s<s (s<s m<n)) = s<s (lemma (s<s p<n) (s<s m<n))

acc : ∀ m n → m < n → Acc m
acc zero    n       m<n = Tick (λ _ ())
acc (suc m) (suc n) m<n = Tick λ p p<sm → acc p n (lemma p<sm m<n)

data _≡_ {A : Prop} (a : A) : A → Set where
  refl : a ≡ a

test : ∀ {m n} (p q : m < n) → p ≡ q
test _ _ = refl
