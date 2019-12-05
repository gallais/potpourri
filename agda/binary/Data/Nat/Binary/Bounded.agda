module Data.Nat.Binary.Bounded where

open import Data.Bool.Base
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base as Vec
  using (Vec; [])
  hiding (module Vec)
  renaming (_∷_ to infixr 10 _∷_)
open import Data.Vec.Properties as Vecₚ
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

infix 1 ⟦_⟧ᵈ
⟦_⟧ᵈ : Digit → ℕ
⟦ d ⟧ᵈ = mux d 0 1

Carry = Digit
Word  = Vec Digit

2ⁿ-1 : ∀ {n} → Word n
2ⁿ-1 = Vec.replicate I

wordToℕ² : ∀ {n} → Word n → ℕ × ℕ
wordToℕ² []      = 0 , 1
wordToℕ² (x ∷ w) = let (n , 2ⁿ) = wordToℕ² w in
                   ⟦ x ⟧ᵈ ℕ.* 2ⁿ ℕ.+ n , 2 ℕ.* 2ⁿ

infix 1 ⟦_⟧ʷ
⟦_⟧ʷ : ∀ {n} → Word n → ℕ
⟦ w ⟧ʷ = proj₁ (wordToℕ² w)

wordToℕ²-sound : ∀ {n} (w : Word n) → proj₂ (wordToℕ² w) ≡ 2 ℕ.^ n
wordToℕ²-sound []      = refl
wordToℕ²-sound (_ ∷ w) = cong (2 ℕ.*_) (wordToℕ²-sound w)

⟦_∷_⟧ʷ-unfold : ∀ {n} x (w : Word n) →
                ⟦ x ∷ w ⟧ʷ ≡ ⟦ x ⟧ᵈ ℕ.* 2 ℕ.^ n ℕ.+ ⟦ w ⟧ʷ
⟦ x ∷ w ⟧ʷ-unfold rewrite wordToℕ²-sound w = refl

_ : ⟦ I ∷ O ∷ I ∷ O ∷ [] ⟧ʷ ≡ 10
_ = refl

hadd : Digit → Digit → Carry × Digit
hadd x y = x ∧ y , x xor y

sucᵈ : Digit → Carry × Digit
sucᵈ d = d , not d

sucᵈ-sound : ∀ d → let (c , u) = sucᵈ d in
             ⟦ c ⟧ᵈ ℕ.* 2 ℕ.+ ⟦ u ⟧ᵈ ≡ suc ⟦ d ⟧ᵈ
sucᵈ-sound O = refl
sucᵈ-sound I = refl

hadd-sound : ∀ x y → let (c , z) = hadd x y in
             ⟦ c ⟧ᵈ ℕ.* 2  ℕ.+ ⟦ z ⟧ᵈ ≡ ⟦ x ⟧ᵈ ℕ.+ ⟦ y ⟧ᵈ
hadd-sound O y = refl
hadd-sound I O = refl
hadd-sound I I = refl

fadd : Digit → Digit → Carry → Carry × Digit
fadd x y cᵢ =
  let (c₀ , d) = hadd x y
      (c₁ , u) = hadd d cᵢ
      in c₀ xor c₁ , u

fadd-sound : ∀ x y cᵢ → let (cₒ , z) = fadd x y cᵢ in
             ⟦ cₒ ⟧ᵈ ℕ.* 2 ℕ.+ ⟦ z ⟧ᵈ ≡ ⟦ x ⟧ᵈ ℕ.+ ⟦ y ⟧ᵈ ℕ.+ ⟦ cᵢ ⟧ᵈ
fadd-sound O y cᵢ = hadd-sound y cᵢ
fadd-sound I O cᵢ = sucᵈ-sound cᵢ
fadd-sound I I cᵢ = refl

rca : ∀ {n} → Word n → Word n → Carry → Carry × Word n
rca {zero}  w₁        w₂        cᵢ = cᵢ , []
rca {suc n} (xₙ ∷ w₁) (yₙ ∷ w₂) cᵢ =
  let (cₙ , w)  = rca w₁ w₂ cᵢ
      (cₒ , zₙ) = fadd xₙ yₙ cₙ
  in cₒ , zₙ ∷ w

module _ where

  open ≡-Reasoning

  rca-sound : ∀ {n} (w₁ w₂ : Word n) cᵢ → let (cₒ , w) = rca w₁ w₂ cᵢ in
              ⟦ cₒ ⟧ᵈ ℕ.* 2 ℕ.^ n ℕ.+ ⟦ w ⟧ʷ ≡ ⟦ w₁ ⟧ʷ ℕ.+ ⟦ w₂ ⟧ʷ ℕ.+ ⟦ cᵢ ⟧ᵈ
  rca-sound {zero}  [] [] cᵢ = let v = mux cᵢ 0 1 in begin
    v ℕ.* 1 ℕ.+ 0 ≡⟨ ℕₚ.+-identityʳ (v ℕ.* 1) ⟩
    v ℕ.* 1       ≡⟨ ℕₚ.*-identityʳ v ⟩
    v             ∎
  rca-sound {suc n} (xₙ ∷ w₁) (yₙ ∷ w₂) cᵢ =
    let (cₙ , w) = rca w₁ w₂ cᵢ; (cₒ , zₙ) = fadd xₙ yₙ cₙ; 2ⁿ = 2 ℕ.^ n
        c₀22ⁿ = (⟦ cₒ ⟧ᵈ ℕ.* 2) ℕ.* 2ⁿ
        xₙ2ⁿ = ⟦ xₙ ⟧ᵈ ℕ.* 2 ℕ.^ n; yₙ2ⁿ = ⟦ yₙ ⟧ᵈ ℕ.* 2 ℕ.^ n
        cₙ2ⁿ = ⟦ cₙ ⟧ᵈ ℕ.* 2 ℕ.^ n; zₙ2ⁿ = ⟦ zₙ ⟧ᵈ ℕ.* 2 ℕ.^ n
        xyₙ2ⁿ = (⟦ xₙ ⟧ᵈ ℕ.+ ⟦ yₙ ⟧ᵈ) ℕ.* 2ⁿ
        rcaₙ = ⟦ w₁ ⟧ʷ ℕ.+ ⟦ w₂ ⟧ʷ ℕ.+ ⟦ cᵢ ⟧ᵈ
    in begin
    ⟦ cₒ ⟧ᵈ ℕ.* 2 ℕ.^ suc n ℕ.+ ⟦ zₙ ∷ w ⟧ʷ
      ≡⟨ cong₂ ℕ._+_ (sym (ℕₚ.*-assoc ⟦ cₒ ⟧ᵈ 2 2ⁿ)) ⟦ zₙ ∷ w ⟧ʷ-unfold ⟩
    c₀22ⁿ ℕ.+ (zₙ2ⁿ ℕ.+ ⟦ w ⟧ʷ)
      ≡⟨ sym (ℕₚ.+-assoc c₀22ⁿ zₙ2ⁿ ⟦ w ⟧ʷ) ⟩
    c₀22ⁿ ℕ.+ zₙ2ⁿ ℕ.+ ⟦ w ⟧ʷ
      ≡⟨ cong (ℕ._+ ⟦ w ⟧ʷ) (sym (ℕₚ.*-distribʳ-+ 2ⁿ (⟦ cₒ ⟧ᵈ ℕ.* 2) ⟦ zₙ ⟧ᵈ)) ⟩
    (⟦ cₒ ⟧ᵈ ℕ.* 2 ℕ.+ ⟦ zₙ ⟧ᵈ) ℕ.* 2ⁿ ℕ.+ ⟦ w ⟧ʷ
      ≡⟨ cong (λ n → n ℕ.* 2ⁿ ℕ.+ ⟦ w ⟧ʷ) (fadd-sound xₙ yₙ cₙ) ⟩
    (⟦ xₙ ⟧ᵈ ℕ.+ ⟦ yₙ ⟧ᵈ ℕ.+ ⟦ cₙ ⟧ᵈ) ℕ.* 2ⁿ ℕ.+ ⟦ w ⟧ʷ
      ≡⟨ cong (ℕ._+ ⟦ w ⟧ʷ) (ℕₚ.*-distribʳ-+ 2ⁿ (⟦ xₙ ⟧ᵈ ℕ.+ ⟦ yₙ ⟧ᵈ) ⟦ cₙ ⟧ᵈ) ⟩
    xyₙ2ⁿ ℕ.+ cₙ2ⁿ ℕ.+ ⟦ w ⟧ʷ
      ≡⟨ ℕₚ.+-assoc xyₙ2ⁿ cₙ2ⁿ ⟦ w ⟧ʷ ⟩
    xyₙ2ⁿ ℕ.+ (cₙ2ⁿ ℕ.+ ⟦ w ⟧ʷ)
      ≡⟨ cong (xyₙ2ⁿ ℕ.+_) (rca-sound w₁ w₂ cᵢ) ⟩
    xyₙ2ⁿ ℕ.+ rcaₙ
      ≡⟨ cong (ℕ._+ (rcaₙ)) (ℕₚ.*-distribʳ-+ 2ⁿ ⟦ xₙ ⟧ᵈ ⟦ yₙ ⟧ᵈ) ⟩
    xₙ2ⁿ ℕ.+ yₙ2ⁿ ℕ.+ rcaₙ
      ≡⟨ ℕₚ.+-assoc xₙ2ⁿ yₙ2ⁿ rcaₙ ⟩
    xₙ2ⁿ ℕ.+ (yₙ2ⁿ ℕ.+ rcaₙ)
      ≡⟨ cong (xₙ2ⁿ ℕ.+_) (ℕₚ.+-comm yₙ2ⁿ rcaₙ) ⟩
    xₙ2ⁿ ℕ.+ (rcaₙ ℕ.+ yₙ2ⁿ)
      ≡⟨ sym (ℕₚ.+-assoc xₙ2ⁿ rcaₙ yₙ2ⁿ) ⟩
    (xₙ2ⁿ ℕ.+ rcaₙ) ℕ.+ yₙ2ⁿ
      ≡⟨ cong (ℕ._+ yₙ2ⁿ) (sym (ℕₚ.+-assoc xₙ2ⁿ (⟦ w₁ ⟧ʷ ℕ.+ ⟦ w₂ ⟧ʷ) ⟦ cᵢ ⟧ᵈ)) ⟩
    xₙ2ⁿ ℕ.+ (⟦ w₁ ⟧ʷ ℕ.+ ⟦ w₂ ⟧ʷ) ℕ.+ ⟦ cᵢ ⟧ᵈ ℕ.+ yₙ2ⁿ
      ≡⟨ cong (λ n → n ℕ.+ ⟦ cᵢ ⟧ᵈ ℕ.+ yₙ2ⁿ) (sym (ℕₚ.+-assoc xₙ2ⁿ ⟦ w₁ ⟧ʷ ⟦ w₂ ⟧ʷ)) ⟩
    (xₙ2ⁿ ℕ.+ ⟦ w₁ ⟧ʷ) ℕ.+ ⟦ w₂ ⟧ʷ ℕ.+ ⟦ cᵢ ⟧ᵈ ℕ.+ yₙ2ⁿ
      ≡⟨ cong (λ n → n ℕ.+ ⟦ w₂ ⟧ʷ ℕ.+ ⟦ cᵢ ⟧ᵈ ℕ.+ yₙ2ⁿ) (sym ⟦ xₙ ∷ w₁ ⟧ʷ-unfold) ⟩
    ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ ⟦ w₂ ⟧ʷ ℕ.+ ⟦ cᵢ ⟧ᵈ ℕ.+ yₙ2ⁿ
      ≡⟨ ℕₚ.+-assoc (⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ ⟦ w₂ ⟧ʷ) ⟦ cᵢ ⟧ᵈ yₙ2ⁿ ⟩
    ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ ⟦ w₂ ⟧ʷ ℕ.+ (⟦ cᵢ ⟧ᵈ ℕ.+ yₙ2ⁿ)
      ≡⟨ cong (λ n → ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ ⟦ w₂ ⟧ʷ ℕ.+ n) (ℕₚ.+-comm ⟦ cᵢ ⟧ᵈ yₙ2ⁿ) ⟩
   ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ ⟦ w₂ ⟧ʷ ℕ.+ (yₙ2ⁿ ℕ.+ ⟦ cᵢ ⟧ᵈ)
      ≡⟨ ℕₚ.+-assoc ⟦ xₙ ∷ w₁ ⟧ʷ ⟦ w₂ ⟧ʷ (yₙ2ⁿ ℕ.+ ⟦ cᵢ ⟧ᵈ) ⟩
    ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ (⟦ w₂ ⟧ʷ ℕ.+ (yₙ2ⁿ ℕ.+ ⟦ cᵢ ⟧ᵈ))
      ≡⟨ cong (⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+_) (sym (ℕₚ.+-assoc ⟦ w₂ ⟧ʷ yₙ2ⁿ ⟦ cᵢ ⟧ᵈ)) ⟩
    ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ ((⟦ w₂ ⟧ʷ ℕ.+ yₙ2ⁿ) ℕ.+ ⟦ cᵢ ⟧ᵈ)
      ≡⟨ cong (λ n → ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ (n ℕ.+ ⟦ cᵢ ⟧ᵈ)) (ℕₚ.+-comm ⟦ w₂ ⟧ʷ yₙ2ⁿ) ⟩
    ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ ((yₙ2ⁿ ℕ.+ ⟦ w₂ ⟧ʷ) ℕ.+ ⟦ cᵢ ⟧ᵈ)
      ≡⟨ cong (λ n → ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ (n ℕ.+ ⟦ cᵢ ⟧ᵈ)) (sym ⟦ yₙ ∷ w₂ ⟧ʷ-unfold) ⟩
    ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ (⟦ yₙ ∷ w₂ ⟧ʷ ℕ.+ ⟦ cᵢ ⟧ᵈ)
      ≡⟨ sym (ℕₚ.+-assoc ⟦ xₙ ∷ w₁ ⟧ʷ ⟦ yₙ ∷ w₂ ⟧ʷ ⟦ cᵢ ⟧ᵈ) ⟩
    ⟦ xₙ ∷ w₁ ⟧ʷ ℕ.+ ⟦ yₙ ∷ w₂ ⟧ʷ ℕ.+ ⟦ cᵢ ⟧ᵈ
      ∎

_ : rca (I ∷ O ∷ O ∷ I ∷ []) -- 9
        (I ∷ I ∷ I ∷ O ∷ []) -- 14
                          I  -- 1
    --------------------------
  ≡ (I , I ∷ O ∷ O ∷ O ∷ []) -- 24
_ = refl

infix 6 _+_
_+_ : ∀ {n} → Word n → Word n → Word n
m + n = proj₂ (rca m n O)

_ : ⟦   I ∷ O ∷ I ∷ O ∷ []     -- 10
    +   O ∷ O ∷ I ∷ I ∷ [] ⟧ʷ  -- 3
     ------------------------
    ≡ ⟦ I ∷ I ∷ O ∷ I ∷ [] ⟧ʷ  -- 13
_ = refl
