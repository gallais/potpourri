module papers.sieve04.Eratosthene where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.Divisibility
open import Data.Empty
open import Data.Product
open import Function
open import Algebra.Structures
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PEq hiding (refl ; trans)

open import papers.sieve04.Data.Stream

open Poset (DecTotalOrder.poset decTotalOrder) hiding (_≤_)

primeUpTo_ : ℕ → (ℕ → Set)
(primeUpTo m) p = ∀ k → 1 < k → k < m → ¬ (k ∣ p)

primeUpTo-≤ : ∀ {m n} → m ≤ n → ∀ {p} → (primeUpTo n) p → (primeUpTo m) p
primeUpTo-≤ m≤n πn k 1<k k<m = πn k 1<k (trans k<m m≤n)

primeUpTo-suc : ∀ {m p} → (primeUpTo m) p → ¬ (m ∣ p) → (primeUpTo suc m) p
primeUpTo-suc πm ¬m∣p k 1<k k<sm with ≤⇒≤′ k<sm
... | ≤′-refl      = ¬m∣p
... | ≤′-step k<′m = πm k 1<k (≤′⇒≤ k<′m)

primeUpTo_-dec : (m : ℕ) → ∀ p → Dec ((primeUpTo m) p)
primeUpTo 0                 -dec p = yes $ λ _ _ ()
primeUpTo 1                 -dec p = yes $ λ _ 1<k k<1 _ → 1+n≰n $ <-trans 1<k k<1
primeUpTo 2                 -dec p =
  yes $ λ _ 1<k k<2 _ → 1+n≰n $ trans 1<k (pred-mono k<2)
primeUpTo 3                 -dec p with 2 ∣? p
... | yes 2∣p = no  $ λ π2 → π2 2 refl refl 2∣p
... | no ¬2∣p =
  yes $ λ k 2≤k k<3 → let k≤2 : k ≤ 2 ; k≤2 = pred-mono k<3
                          2≡k : 2 ≡ k ; 2≡k = antisym 2≤k k≤2
                      in subst (¬_ ∘ (_∣ p)) 2≡k ¬2∣p
primeUpTo suc m@(suc (suc (suc _))) -dec p with primeUpTo m -dec p | m ∣? p
... | yes πm | yes m∣p = no (λ πsm → πsm m (s≤s (s≤s z≤n)) refl m∣p)
... | yes πm | no ¬m∣p = yes (primeUpTo-suc πm ¬m∣p)
... | no ¬πm | _       = no (¬πm ∘ primeUpTo-≤ (n≤1+n m))

preprime : ℕ → Set
preprime n = (primeUpTo n) n

preprime-dec : ∀ n → Dec (preprime n)
preprime-dec n = primeUpTo n -dec n


infixl 8 _!
_! : ℕ → ℕ
zero      ! = 1
m@(suc n) ! = n ! * m

1≤n! : ∀ n → 1 ≤ n !
1≤n! zero    = s≤s z≤n
1≤n! (suc n) = 1≤n! n *-mono s≤s z≤n

n≤n! : ∀ n → n ≤ n !
n≤n! zero      = z≤n
n≤n! m@(suc n) = coerce $ 1≤n! n *-mono refl
  where coerce = subst (_≤ m !) (+-comm (suc n) 0)

open PEq.≡-Reasoning

∣-*₁ : ∀ {m n p} → m ∣ n → m ∣ n * p
∣-*₁ {m} {n} {p} (divides q eq) = divides (p * q) $
  begin
    n * p       ≡⟨ cong (_* p) eq     ⟩
    q * m * p   ≡⟨ *-comm (q * m) p     ⟩
    p * (q * m) ≡⟨ sym (*-assoc p q m) ⟩
    p * q * m
  ∎

∣-*₂ : ∀ {m n p} → m ∣ p → m ∣ n * p
∣-*₂ {m} {n} {p} (divides q eq) = divides (n * q) $
  begin
    n * p       ≡⟨ cong (n *_) eq ⟩
    n * (q * m) ≡⟨ sym (*-assoc n q m) ⟩
    n * q * m
  ∎

∣-! : ∀ {m n} → 0 < m → m ≤′ n → m ∣ n !
∣-! {zero}  0<0 ≤′-refl        = ⊥-elim $ 1+n≰n 0<0
∣-! {suc m} 0<m ≤′-refl        = ∣-* (m !)
∣-!         0<m (≤′-step m≤′n) = ∣-*₁ (∣-! 0<m m≤′n)

infix 4 _≤₂_ _<₂_
data _≤₂_ (m : ℕ) : (n : ℕ) → Set where
  ≤₂-refl : m ≤₂ m
  ≤₂-step : ∀ {n} → suc m ≤₂ n → m ≤₂ n

_<₂_ : (m n : ℕ) → Set
m <₂ n = suc m ≤₂ n

≤₂-trans : ∀ {m n p} → m ≤₂ n → n ≤₂ p → m ≤₂ p
≤₂-trans ≤₂-refl     q = q
≤₂-trans (≤₂-step p) q = ≤₂-step (≤₂-trans p q)

+-≤₂ : ∀ {m n p q} → m ≤₂ n → p ≤₂ q → m + p ≤₂ n + q
+-≤₂ (≤₂-step p) q       = ≤₂-step (+-≤₂ p q)
+-≤₂ ≤₂-refl     ≤₂-refl = ≤₂-refl
+-≤₂ {p} {.p} {m} {n} ≤₂-refl (≤₂-step q) =
  ≤₂-step (subst (_≤₂ p + n) (+-suc p m) (+-≤₂ {p} ≤₂-refl q))

suc-≤₂ : ∀ {m n} → m ≤₂ n → suc m ≤₂ suc n
suc-≤₂ = +-≤₂ (≤₂-refl {1})

0≤₂n : ∀ n → 0 ≤₂ n
0≤₂n zero    = ≤₂-refl
0≤₂n (suc n) = ≤₂-step (suc-≤₂ (0≤₂n n))

≤⇒≤₂ : {m n : ℕ} → m ≤ n → m ≤₂ n
≤⇒≤₂ z≤n     = 0≤₂n _
≤⇒≤₂ (s≤s p) = +-≤₂ (≤₂-refl {1}) (≤⇒≤₂ p)

≤₂⇒≤ : {m n : ℕ} → m ≤₂ n → m ≤ n
≤₂⇒≤ ≤₂-refl     = refl
≤₂⇒≤ (≤₂-step p) = trans (n≤1+n _) (≤₂⇒≤ p)

module _ {ℓ} {P : ℕ → Set ℓ} (P? : ∀ n → Dec (P n)) where

  -- Here we use whichever definition of _≤_ is the easiest to work with
  -- given that we iterate from the bottom up, _≤₂_ is our order of choice.

  private
    contradiction : ∀ {ℓ′} {P : ℕ → Set ℓ′} {m} k → m ≤₂ k → k <₂ m → P k
    contradiction k m≤k k<m = ⊥-elim $ 1+n≰n $ ≤₂⇒≤ $ ≤₂-trans (suc-≤₂ m≤k) k<m

  ¬∀⇒∃ : {m n : ℕ} → m ≤₂ n →
         ¬ (∀ k → m ≤₂ k → k <₂ n → P k) →
         ∃ λ k → m ≤₂ k × k <₂ n × P k
         × ∀ l → m ≤₂ l → l <₂ k → ¬ P l
  ¬∀⇒∃     ≤₂-refl        ¬∀ = ⊥-elim (¬∀ contradiction)
  ¬∀⇒∃ {m} (≤₂-step m≤′n) ¬∀ with P? m
  ... | yes pm = m , ≤₂-refl , m≤′n , pm , contradiction
  ... | no ¬pm =
    let (k , sm≤k , k<n , Pk , ∀¬P) = ¬∀⇒∃ m≤′n (λ ∀P → {!!}) -- TODO
    in k , ≤₂-step sm≤k , k<n , Pk , λ
    { .m ≤₂-refl        l<n → ¬pm
    ; l (≤₂-step sl≤₂m) l<n → ∀¬P l sl≤₂m l<n }

preprime-split : ∀ n → ¬ (preprime n) → ∃ λ m → preprime m × 1 < m × m < n
preprime-split = {!!}



-- Plan: test all k such that m ≤ k and k ≤ m !

infinite-preprime : ∀ m → ∃ λ n → m ≤ n × preprime n
infinite-preprime m = {!!}
