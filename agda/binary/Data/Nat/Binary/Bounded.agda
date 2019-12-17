module Data.Nat.Binary.Bounded where

open import Data.Bool.Base
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _+_; _*_; _^_)
import Data.Nat.Properties as ℕₚ
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂)
open import Function

open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

Digit : Set
Digit = Bool

pattern O = false
pattern I = true

mux : ∀ {a} {A : Set a} → Digit → A → A → A
mux O x y = x
mux I x y = y

double : ℕ → ℕ
double m = m + m

unfold-double : ∀ m → double m ≡ 2 * m
unfold-double m = cong (m +_) (sym (ℕₚ.+-identityʳ _))

*-double : ∀ m n → m * double n ≡ double (m * n)
*-double m n = ℕₚ.*-distribˡ-+ m n n

double-+ : ∀ m n → double (m + n) ≡ double m + double n
double-+ m n = begin
  m + n + (m + n)   ≡⟨ ℕₚ.+-assoc m n (m + n) ⟩
  m + (n + (m + n)) ≡⟨ cong (m +_) (ℕₚ.+-comm n (m + n)) ⟩
  m + (m + n + n)   ≡⟨ cong (m +_) (ℕₚ.+-assoc m n n) ⟩
  m + (m + (n + n)) ≡⟨ sym $ ℕₚ.+-assoc m m (n + n) ⟩
  m + m + (n + n)   ∎ where open ≡-Reasoning

2^_ : ℕ → ℕ
2^ zero  = 1
2^ suc n = double (2^ n)

unfold-2^ : ∀ n → 2^ n ≡ 2 ^ n
unfold-2^ zero    = refl
unfold-2^ (suc n) = begin
  2^ suc n       ≡⟨⟩
  double (2^ n)  ≡⟨ cong double (unfold-2^ n) ⟩
  double (2 ^ n) ≡⟨ unfold-double (2 ^ n) ⟩
  2 * 2 ^ n      ≡⟨⟩
  (2 ^ suc n)    ∎ where open ≡-Reasoning

infix 1 ⟦_⟧ᵈ
⟦_⟧ᵈ : Digit → ℕ
⟦ O ⟧ᵈ = 0
⟦ I ⟧ᵈ = 1

Carry = Digit

infixl 5 _▹_
data Word : ℕ → Set where
  []  : Word 0
  _▹_ : ∀ {n} → Word n → Digit → Word (suc n)

2ⁿ-1 : ∀ {n} → Word n
2ⁿ-1 {zero}  = []
2ⁿ-1 {suc n} = 2ⁿ-1 ▹ I

infix 1 ⟦_⟧ʷ
⟦_⟧ʷ : ∀ {n} → Word n → ℕ
⟦ []    ⟧ʷ = 0
⟦ w ▹ d ⟧ʷ = ⟦ d ⟧ᵈ + double ⟦ w ⟧ʷ

_ : ⟦ [] ▹ I ▹ O ▹ I ▹ O ⟧ʷ ≡ 10
_ = refl

hadd : Digit → Digit → Carry × Digit
hadd x y = x ∧ y , x xor y

sucᵈ : Digit → Carry × Digit
sucᵈ d = d , not d

sucᵈ-sound : ∀ d → let (c , u) = sucᵈ d in
             double ⟦ c ⟧ᵈ + ⟦ u ⟧ᵈ ≡ suc ⟦ d ⟧ᵈ
sucᵈ-sound O = refl
sucᵈ-sound I = refl

hadd-sound : ∀ x y → let (c , z) = hadd x y in
             double ⟦ c ⟧ᵈ  + ⟦ z ⟧ᵈ ≡ ⟦ x ⟧ᵈ + ⟦ y ⟧ᵈ
hadd-sound O y = refl
hadd-sound I O = refl
hadd-sound I I = refl

fadd : Digit → Digit → Carry → Carry × Digit
fadd x y cᵢ =
  let (c₀ , d) = hadd x y
      (c₁ , u) = hadd d cᵢ
      in c₀ xor c₁ , u

fadd-sound : ∀ x y cᵢ → let (cₒ , z) = fadd x y cᵢ in
             double ⟦ cₒ ⟧ᵈ + ⟦ z ⟧ᵈ ≡ ⟦ x ⟧ᵈ + ⟦ y ⟧ᵈ + ⟦ cᵢ ⟧ᵈ
fadd-sound O y cᵢ = hadd-sound y cᵢ
fadd-sound I O cᵢ = sucᵈ-sound cᵢ
fadd-sound I I cᵢ = refl

rca : ∀ {n} → Word n → Word n → Carry → Carry × Word n
rca {zero}  ds        es        cᵢ = cᵢ , []
rca {suc n} (ds ▹ d₀) (es ▹ e₀) cᵢ =
  let (c₁ , r₀) = fadd d₀ e₀ cᵢ
      (cₒ , rs) = rca ds es c₁
  in cₒ , rs ▹ r₀

module _ where

  open ≡-Reasoning

  rca-sound : ∀ {n} (ds es : Word n) cᵢ → let (cₒ , rs) = rca ds es cᵢ in
              ⟦ cₒ ⟧ᵈ * 2^ n + ⟦ rs ⟧ʷ ≡ ⟦ ds ⟧ʷ + ⟦ es ⟧ʷ + ⟦ cᵢ ⟧ᵈ
  rca-sound {zero}  [] [] cᵢ
    with ⟦cᵢ⟧ ← ⟦ cᵢ ⟧ᵈ
    = begin
    ⟦cᵢ⟧ * 1 + 0 ≡⟨ ℕₚ.+-identityʳ (⟦cᵢ⟧ * 1) ⟩
    ⟦cᵢ⟧ * 1     ≡⟨ ℕₚ.*-identityʳ ⟦cᵢ⟧ ⟩
    ⟦cᵢ⟧         ∎
  rca-sound {suc n} (ds ▹ d₀) (es ▹ e₀) cᵢ
    with c₁  ← proj₁ (fadd d₀ e₀ cᵢ)
       | r₀  ← proj₂ (fadd d₀ e₀ cᵢ)
       | eq₀ ← fadd-sound d₀ e₀ cᵢ
    with cₒ  ← proj₁ (rca ds es c₁)
       | rs  ← proj₂ (rca ds es c₁)
       | ih  ← rca-sound ds es c₁
    with ⟦d₀⟧ ← ⟦ d₀ ⟧ᵈ
       | ⟦e₀⟧ ← ⟦ e₀ ⟧ᵈ
       | ⟦cₒ⟧ ← ⟦ cₒ ⟧ᵈ
       | ⟦cᵢ⟧ ← ⟦ cᵢ ⟧ᵈ
       | ⟦c₁⟧ ← ⟦ c₁ ⟧ᵈ
       | ⟦r₀⟧ ← ⟦ r₀ ⟧ᵈ
       | ⟦rs⟧ ← ⟦ rs ⟧ʷ
       | ⟦ds⟧ ← ⟦ ds ⟧ʷ
       | ⟦es⟧ ← ⟦ es ⟧ʷ
    = begin
    ⟦cₒ⟧ * (double (2^ n)) + (⟦r₀⟧ + double ⟦rs⟧)
      ≡⟨ cong (_+ (⟦r₀⟧ + double ⟦rs⟧)) (*-double ⟦cₒ⟧ (2^ n)) ⟩
    double (⟦cₒ⟧ * 2^ n) + (⟦r₀⟧ + double ⟦rs⟧)
      ≡⟨ cong ((double (⟦cₒ⟧ * 2^ n)) +_) (ℕₚ.+-comm ⟦r₀⟧ (double ⟦rs⟧)) ⟩
    double (⟦cₒ⟧ * 2^ n) + (double ⟦rs⟧ + ⟦r₀⟧)
      ≡⟨ sym $ ℕₚ.+-assoc (double (⟦cₒ⟧ * 2^ n)) (double ⟦rs⟧) ⟦r₀⟧ ⟩
    double (⟦cₒ⟧ * 2^ n) + double ⟦rs⟧ + ⟦r₀⟧
      ≡⟨ cong (_+ ⟦r₀⟧) (sym $ double-+ (⟦cₒ⟧ * 2^ n) ⟦rs⟧) ⟩
    double (⟦cₒ⟧ * (2^ n) + ⟦rs⟧) + ⟦r₀⟧
      ≡⟨ cong (λ p → double p + ⟦r₀⟧) ih ⟩
    double (⟦ds⟧ + ⟦es⟧ + ⟦c₁⟧) + ⟦r₀⟧
      ≡⟨ cong (_+ ⟦r₀⟧) (double-+ (⟦ds⟧ + ⟦es⟧) ⟦c₁⟧) ⟩
    double (⟦ds⟧ + ⟦es⟧) + double ⟦c₁⟧ + ⟦r₀⟧
      ≡⟨ ℕₚ.+-assoc (double (⟦ds⟧ + ⟦es⟧)) (double ⟦c₁⟧) ⟦r₀⟧ ⟩
    double (⟦ds⟧ + ⟦es⟧) + (double ⟦c₁⟧ + ⟦r₀⟧)
      ≡⟨ cong ((double (⟦ds⟧ + ⟦es⟧)) +_) eq₀ ⟩
    double (⟦ds⟧ + ⟦es⟧) + (⟦d₀⟧ + ⟦e₀⟧ + ⟦cᵢ⟧)
      ≡⟨ cong ((double (⟦ds⟧ + ⟦es⟧)) +_) (ℕₚ.+-assoc ⟦d₀⟧ ⟦e₀⟧ ⟦cᵢ⟧) ⟩
    double (⟦ds⟧ + ⟦es⟧) + (⟦d₀⟧ + (⟦e₀⟧ + ⟦cᵢ⟧))
      ≡⟨ sym $ ℕₚ.+-assoc (double (⟦ds⟧ + ⟦es⟧)) ⟦d₀⟧ (⟦e₀⟧ + ⟦cᵢ⟧) ⟩
    double (⟦ds⟧ + ⟦es⟧) + ⟦d₀⟧ + (⟦e₀⟧ + ⟦cᵢ⟧)
      ≡⟨ cong (_+ (⟦e₀⟧ + ⟦cᵢ⟧)) (ℕₚ.+-comm (double (⟦ds⟧ + ⟦es⟧)) ⟦d₀⟧) ⟩
    ⟦d₀⟧ + double (⟦ds⟧ + ⟦es⟧) + (⟦e₀⟧ + ⟦cᵢ⟧)
      ≡⟨ cong (λ p → ⟦d₀⟧ + p + (⟦e₀⟧ + ⟦cᵢ⟧)) (double-+ ⟦ds⟧ ⟦es⟧) ⟩
    ⟦d₀⟧ + (double ⟦ds⟧ + double ⟦es⟧) + (⟦e₀⟧ + ⟦cᵢ⟧)
      ≡⟨ ℕₚ.+-assoc ⟦d₀⟧ (double ⟦ds⟧ + double ⟦es⟧) (⟦e₀⟧ + ⟦cᵢ⟧) ⟩
    ⟦d₀⟧ + (double ⟦ds⟧ + double ⟦es⟧ + (⟦e₀⟧ + ⟦cᵢ⟧))
      ≡⟨ cong (⟦d₀⟧ +_) (ℕₚ.+-assoc (double ⟦ds⟧) (double ⟦es⟧) (⟦e₀⟧ + ⟦cᵢ⟧)) ⟩
    ⟦d₀⟧ + (double ⟦ds⟧ + (double ⟦es⟧ + (⟦e₀⟧ + ⟦cᵢ⟧)))
      ≡⟨ sym $ ℕₚ.+-assoc ⟦d₀⟧ (double ⟦ds⟧) (double ⟦es⟧ + (⟦e₀⟧ + ⟦cᵢ⟧)) ⟩
    ⟦d₀⟧ + double ⟦ds⟧ + (double ⟦es⟧ + (⟦e₀⟧ + ⟦cᵢ⟧))
      ≡⟨ cong (λ p → ⟦d₀⟧ + double ⟦ds⟧ + p) (sym $ ℕₚ.+-assoc (double ⟦es⟧) ⟦e₀⟧ ⟦cᵢ⟧) ⟩
    ⟦d₀⟧ + double ⟦ds⟧ + (double ⟦es⟧ + ⟦e₀⟧ + ⟦cᵢ⟧)
      ≡⟨ cong (λ p → ⟦d₀⟧ + double ⟦ds⟧ + (p + ⟦cᵢ⟧)) (ℕₚ.+-comm (double ⟦es⟧) ⟦e₀⟧) ⟩
    ⟦d₀⟧ + double ⟦ds⟧ + (⟦e₀⟧ + double ⟦es⟧ + ⟦cᵢ⟧)
      ≡⟨ sym $ ℕₚ.+-assoc (⟦d₀⟧ + double ⟦ds⟧) (⟦e₀⟧ + double ⟦es⟧) ⟦cᵢ⟧ ⟩
    ⟦d₀⟧ + double ⟦ds⟧ + (⟦e₀⟧ + double ⟦es⟧) + ⟦cᵢ⟧
      ∎

_ : rca ([] ▹ I ▹ O ▹ O ▹ I) -- 9
        ([] ▹ I ▹ I ▹ I ▹ O) -- 14
                          I  -- 1
    --------------------------
  ≡ (I , [] ▹ I ▹ O ▹ O ▹ O) -- 24
_ = refl

infix 3 _+ʷ_
_+ʷ_ : ∀ {n} → Word n → Word n → Word n
m +ʷ n = proj₂ (rca m n O)

_ : ⟦   [] ▹ I ▹ O ▹ I ▹ O     -- 10
    +ʷ  [] ▹ O ▹ O ▹ I ▹ I ⟧ʷ  -- 3
     ------------------------
    ≡ ⟦ [] ▹ I ▹ I ▹ O ▹ I ⟧ʷ  -- 13
_ = refl
