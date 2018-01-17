-- Based on: https://www.math.hmc.edu/funfacts/ffiles/20004.5.shtml

module papers.fibonacci.Fib where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.GCD
open import Data.Nat.Divisibility

fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib (suc n) + fib n

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

gcd-fib-pred : ∀ n → GCD (fib (suc n)) (fib n) 1
gcd-fib-pred 0       = GCD.is (divides 1 refl , divides 0 refl) proj₁
gcd-fib-pred (suc n) = GCD.sym (GCD.step (gcd-fib-pred n))

fib-+s-expand : ∀ m n →
  fib (m + suc n) ≡ fib (suc m) * fib (suc n) + fib m * fib n
fib-+s-expand 0       n = begin
  fib (suc n)         ≡⟨ sym (+-identityʳ _) ⟩
  fib (suc n) + 0     ≡⟨ sym (+-identityʳ _) ⟩
  fib (suc n) + 0 + 0 ∎
fib-+s-expand (suc m) n = begin
  let fm = fib m ; fn = fib n ; fsm = fib (suc m) ; fsn = fib (suc n) in
  fib (suc (m + suc n))             ≡⟨ cong fib (sym (+-suc m (suc n))) ⟩
  fib (m + suc (suc n))             ≡⟨ fib-+s-expand m (suc n) ⟩
  fsm * (fsn + fn) + fm * fsn       ≡⟨ cong (_+ (fm * fsn)) (*-distribˡ-+ fsm fsn fn) ⟩
  fsm * fsn + fsm * fn + fm * fsn   ≡⟨ cong (_+ (fm * fsn)) (+-comm (fsm * fsn) _) ⟩
  fsm * fn + fsm * fsn + fm * fsn   ≡⟨ +-assoc (fsm * fn) _ _ ⟩
  fsm * fn + (fsm * fsn + fm * fsn) ≡⟨ cong ((fsm * fn) +_) (sym $ *-distribʳ-+ fsn fsm fm) ⟩
  fsm * fn + (fsm + fm) * fsn       ≡⟨ +-comm (fsm * fn) _ ⟩
  fib (2 + m) * fsn + fsm * fn      ∎

fib∣fib[q*] : ∀ m q → fib m ∣ fib (q * m)
fib∣fib[q*] m zero    = fib m ∣0
fib∣fib[q*] m (suc q) with q * m | fib∣fib[q*] m q
... | zero  | _  = subst (λ m′ → fib m ∣ fib m′) (sym (+-identityʳ m)) n∣n
... | suc p | ih = subst (fib m ∣_) (sym (fib-+s-expand m p)) $
                     ∣m∣n⇒∣m+n {m = fib (suc m) * fib (suc p)}
                       (∣n⇒∣m*n (fib (suc m)) ih)
                       (m|m*n (fib p))

fib-div : ∀ m n → m ∣ n → fib m ∣ fib n
fib-div m n (divides q eq) = subst (λ m′ → fib m ∣ fib m′) (sym eq) (fib∣fib[q*] m q)

