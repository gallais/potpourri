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

infix 1 _⊥_
_⊥_ : ℕ → ℕ → Set
m ⊥ n = GCD m n 1

∣m*n∧m⊥⇒∣n : ∀ {d m n} → d ∣ m * n → d ⊥ m → d ∣ n
∣m*n∧m⊥⇒∣n {d} {m} {n} d∣m*n d⊥m with Bézout.identity d⊥m
... | Bézout.+- x y eq = ∣-∸ d∣y*m*n+n d∣y*m*n where

   prf : y * m * n + n ≡ x * d * n
   prf = begin
     y * m * n + n ≡⟨ +-comm (y * m * n) n ⟩
     n + y * m * n ≡⟨ cong (_* n) eq ⟩
     x * d * n ∎

   d∣y*m*n+n : d ∣ y * m * n + n
   d∣y*m*n+n rewrite prf = ∣m⇒∣m*n n (n|m*n x)

   d∣y*m*n : d ∣ y * m * n
   d∣y*m*n rewrite *-assoc y m n = ∣n⇒∣m*n y d∣m*n

... | Bézout.-+ x y eq = ∣-∸ d∣x*d*n+n d∣x*d*n where

  prf : x * d * n + n ≡ y * (m * n)
  prf = begin
    x * d * n + n ≡⟨ +-comm (x * d * n) n ⟩
    n + x * d * n ≡⟨ cong (_* n) eq ⟩
    y * m * n     ≡⟨ *-assoc y m n ⟩
    y * (m * n)   ∎

  d∣x*d*n+n : d ∣ x * d * n + n
  d∣x*d*n+n rewrite prf = ∣n⇒∣m*n y d∣m*n

  d∣x*d*n : d ∣ x * d * n
  d∣x*d*n = ∣m⇒∣m*n n (n|m*n x)

∣n∧n⊥p⇒⊥p : ∀ {m n p} → m ∣ n → n ⊥ p → m ⊥ p
∣n∧n⊥p⇒⊥p m∣n (GCD.is _ n⊥p) = GCD.is (1∣ _ , 1∣ _) $ uncurry
                             $ λ d∣m d∣p → n⊥p (∣-trans d∣m m∣n , d∣p)

lemma' : ∀ {m n p g} → GCD m n 1 → GCD m p g → GCD m (n * p) g
lemma' {n = n} (GCD.is _ cp) (GCD.is (g∣m , g∣p) supg) =
  GCD.is (g∣m , ∣n⇒∣m*n n g∣p) $ λ {d} → uncurry $ λ d∣m d∣n*p →
    let (q , qgcd@(GCD.is (q∣d , q∣n) supq)) = gcd d n
        eq                                   = ∣1⇒≡1 (cp (∣-trans q∣d d∣m , q∣n))
    in curry supg d∣m (∣m*n∧m⊥⇒∣n d∣n*p (subst (GCD d n) eq qgcd))

gcd-fib : ∀ m q r {g} → GCD (fib m) (fib r) g → GCD (fib m) (fib (m * q + r)) g
gcd-fib m 0 r isGCD rewrite *-zeroʳ m = isGCD
gcd-fib m (suc q) 0 isGCD with fib-div m (m * suc q) (divides (suc q) (*-comm m _))
... | divides p eq = cast $ GCD.steps p isGCD where

  cast = subst (λ p → GCD (fib m) p _)
       $ trans (+-identityʳ (p * fib m))
       $ trans (sym eq) (cong fib $ sym (+-identityʳ (m * suc q)))

gcd-fib m (suc q) (suc r) isGCD with fib-div m (m * suc q) (divides (suc q) (*-comm m _))
... | divides p eq = cast $ GCD.steps (p * fib r) $ lemma' prf isGCD where

  prf : GCD (fib m) (fib (suc (m * suc q))) 1
  prf = ∣n∧n⊥p⇒⊥p (fib-div m (m * suc q) (m|m*n (suc q)))
      $ GCD.sym (gcd-fib-pred (m * suc q))

  t : ℕ
  t =  fib (suc (m * suc q)) * fib (suc r)

  expand : fib (m * suc q + suc r) ≡ (p * fib r) * fib m + t
  expand = begin let m*sq = m * suc q in
    fib (m*sq + suc r)      ≡⟨ fib-+s-expand (m*sq) r ⟩
    t + fib m*sq * fib r    ≡⟨ cong (λ p → t + p * fib r) eq ⟩
    t + p * fib m * fib r   ≡⟨ cong (λ p → t + p * fib r) (*-comm p (fib m)) ⟩
    t + fib m * p * fib r   ≡⟨ cong (t +_) (*-assoc (fib m) p (fib r)) ⟩
    t + fib m * (p * fib r) ≡⟨ cong (t +_) (*-comm (fib m) (p * fib r)) ⟩
    t + (p * fib r) * fib m ≡⟨ +-comm t ((p * fib r) * fib m) ⟩
    p * fib r * fib m + t   ∎

  cast = subst (λ p → GCD (fib m) p _) (sym expand)


