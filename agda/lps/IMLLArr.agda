module lps.IMLLArr where

open import lib.Context
open import Data.Nat

open Context
open Context.Pointwise

open import Function
open import lib.Function

open import Relation.Binary.PropositionalEquality

infixl 40 _`⊗_ _`&_
infixr 30 _`⊸_

data ty : Set where
  `κ : ℕ → ty
  _`⊗_ _`&_ _`⊸_ : (σ τ : ty) → ty


data Cover : ty → Set where
  `κ     : (k : ℕ) → Cover $ `κ k
  _`⊗_   : {a b : ty} (A : Cover a) (B : Cover b) → Cover $ a `⊗ b
  [_]`⊗_ : (a : ty) {b : ty} (B : Cover b) → Cover $ a `⊗ b
  _`⊗[_] : {a : ty} (A : Cover a) (b : ty) → Cover $ a `⊗ b
     -- BOTH sides of an additive conjunction can be used if and only if
     -- they are entirely eaten up. Hence the lack of recursive arg.
  _`&_   : (a b : ty) → Cover $ a `& b
  _`&[_] : {a : ty} (A : Cover a) (b : ty) → Cover $ a `& b
  [_]`&_  : (a : ty) {b : ty} (B : Cover b) → Cover $ a `& b
     -- the only way to use an arrow type is to use its codomain
  ]_[`⊸_ : (a : ty) {b : ty} (B : Cover b) → Cover $ a `⊸ b

data Usage : ty → Set where
  [_] : (a : ty) → Usage a
  ]_[ : {a : ty} (A : Cover a) → Usage a

Usages : Con ty → Set
Usages = PCon Usage

mutual

  infix 4 [_]∋_∈_,_
  data [_]∋_∈_,_ : (a : ty) (k : ℕ) (A : Cover a) (G : Con ty) → Set where
    `κ      : (k : ℕ) → [ `κ k ]∋ k ∈ `κ k , ε
    _`&[_]  : {k : ℕ} {a : ty} {A : Cover a} {G : Con ty}
              (prA : [ a ]∋ k ∈ A , G) (b : ty) → [ a `& b ]∋ k ∈ A `&[ b ] , G
    [_]`&_  : {k : ℕ} (a : ty) {b : ty} {B : Cover b} {G : Con ty}
              (prB : [ b ]∋ k ∈ B , G) → [ a `& b ]∋ k ∈ [ a ]`& B , G
    _`⊗[_]  : {k : ℕ} {a : ty} {A : Cover a} {G : Con ty}
              (prA : [ a ]∋ k ∈ A , G) (b : ty) → [ a `⊗ b ]∋ k ∈ A `⊗[ b ] , G
    [_]`⊗_  : {k : ℕ} (a : ty) {b : ty} {B : Cover b} {G : Con ty}
              (prB : [ b ]∋ k ∈ B , G) → [ a `⊗ b ]∋ k ∈ [ a ]`⊗ B , G
    _`⊸_   : {k : ℕ} (a : ty) {b : ty} {B : Cover b} {G : Con ty}
              (prB : [ b ]∋ k ∈ B , G) → [ a `⊸ b ]∋ k ∈ ] a [`⊸ B , G ∙ a

  data ]_[∋_∈_,_ : {a : ty} (A : Cover a) (k : ℕ)
                   (A′ : Cover a) (G : Con ty) → Set where
    [_]`⊗_ : {k : ℕ} (a : ty) {b : ty} {B B′ : Cover b} {G : Con ty} →
             ] B [∋ k ∈ B′ , G → ] [ a ]`⊗ B [∋ k ∈ [ a ]`⊗ B′ , G
    _`⊗[_] : {k : ℕ} {a : ty} {A A′ : Cover a} {G : Con ty} →
             (prA : ] A [∋ k ∈ A′ , G) (b : ty) → ] A `⊗[ b ] [∋ k ∈ A′ `⊗[ b ] , G
    _`⊗₂_  : {k : ℕ} {a b : ty} (A : Cover a) {B B′ : Cover b} {G : Con ty} →
             ] B [∋ k ∈ B′ , G → ] A `⊗ B [∋ k ∈ A `⊗ B′ , G
    _`⊗₁_  : {k : ℕ} {a b : ty} {A A′ : Cover a} {G : Con ty} →
             (prA : ] A [∋ k ∈ A′ , G) (B : Cover b) → ] A `⊗ B [∋ k ∈ A′ `⊗ B , G
    ]_[`⊗_ : {k : ℕ} {a b : ty} {A : Cover a} {G : Con ty} →
             (prA : [ a ]∋ k ∈ A , G) (B : Cover b) → ] [ a ]`⊗ B [∋ k ∈ A `⊗ B , G
    _`⊗]_[ : {k : ℕ} {a b : ty} (A : Cover a) {B : Cover b} {G : Con ty} →
             (prB : [ b ]∋ k ∈ B , G) → ] A `⊗[ b ] [∋ k ∈ A `⊗ B , G
    [_]`&_ : {k : ℕ} (a : ty) {b : ty} {B B′ : Cover b} {G : Con ty} →
             ] B [∋ k ∈ B′ , G → ] [ a ]`& B [∋ k ∈ [ a ]`& B′ , G
    _`&[_] : {k : ℕ} {a : ty} {A A′ : Cover a} {G : Con ty} →
             (prA : ] A [∋ k ∈ A′ , G) (b : ty) → ] A `&[ b ] [∋ k ∈ A′ `&[ b ] , G
    ]_[`⊸_ : {k : ℕ} (a : ty) {b : ty} {B B′ : Cover b} {G : Con ty}
              (prB : ] B [∋ k ∈ B′ , G) → ] ] a [`⊸ B [∋ k ∈ ] a [`⊸ B′ , G
 

data _∋_∈_,_ {a : ty} : (A : Usage a) (k : ℕ)
             (A′ : Usage a) (G : Con ty) → Set where
  [_] : {A : Cover a} {k : ℕ} {G : Con ty} →
        [ a ]∋ k ∈ A , G → [ a ] ∋ k ∈ ] A [ , G
  ]_[ : {A A′ : Cover a} {k : ℕ} {G : Con ty} →
        ] A [∋ k ∈ A′ , G → ] A [ ∋ k ∈ ] A′ [ , G

data _∋s_s∈_,_ : {γ : Con ty} (Γ : Usages γ) (k : ℕ)
                 (Δ : Usages γ) (G : Con ty) → Set where
  zro : {γ : Con ty} {a : ty} {k : ℕ} {Γ : Usages γ} {A A′ : Usage a} {G : Con ty} →
        A ∋ k ∈ A′ , G → Γ ∙ A ∋s k s∈ Γ ∙ A′ , G
  suc : {γ : Con ty} {a : ty} {k : ℕ} {Γ Δ : Usages γ} {A : Usage a} {G : Con ty} →
        Γ ∋s k s∈ Δ , G → Γ ∙ A ∋s k s∈ Δ ∙ A , G

data isCovered : {a : ty} (A : Cover a) → Set where
  `κ      : (k : ℕ) → isCovered $ `κ k
  ]_[`⊸_ : (a : ty) {b : ty} {B : Cover b} →
            isCovered B → isCovered $ ] a [`⊸ B
  _`⊗_    : {a b : ty} {A : Cover a} {B : Cover b} →
            isCovered A → isCovered B → isCovered $ A `⊗ B
  _`&_    : (a b : ty) → isCovered $ a `& b
  [_]`&_  : (a : ty) {b : ty} {B : Cover b} →
            isCovered B → isCovered $ [ a ]`& B
  _`&[_]  : {a : ty} {A : Cover a} (iCA : isCovered A) →
            {b : ty} → isCovered $ A `&[ b ]

data isUsed {a : ty} : (A : Usage a) → Set where
  ]_[ : {A : Cover a} (prA : isCovered A) → isUsed ] A [


-- to be defined
infix 4 _≡_⊙_
data _≡_⊙_ : {γ : Con ty} (E Δ₁ Δ₂ : Usages γ) → Set where

mutual

  infix 1 _⊢_⊣_
  data _⊢_⊣_ {γ : Con ty} (Γ : Usages γ) : (σ : ty) (Δ : Usages γ) → Set where
    `κ[_]$_  : {k : ℕ} {Δ E : Usages γ} {G : Con ty} →
               Γ ∋s k s∈ Δ , G → Δ ⊢s G s⊣ E → Γ ⊢ `κ k ⊣ E
    _`⊗_     : {a b : ty} {Δ E : Usages γ}
               (ta : Γ ⊢ a ⊣ Δ) (tb : Δ ⊢ b ⊣ E) → Γ ⊢ a `⊗ b ⊣ E
    _`&_     : {a b : ty} {Δ₁ Δ₂ Δ : Usages γ} {H₁ H₂ : Con ty}
               (ta : Γ ⊢ a ⊣ Δ₁) (tb : Γ ⊢ b ⊣ Δ₂) (sync : Δ ≡ Δ₁ ⊙ Δ₂) →
               Γ ⊢ a `& b ⊣ Δ
    _`⊸_    : {a b : ty} {Δ : Usages γ} {A : Usage a}
               (iuA : isUsed A) (body : Γ ∙ [ a ] ⊢ b ⊣ Δ ∙ A) → Γ ⊢ a `⊸ b ⊣ Δ

  data _⊢s_s⊣_ {γ : Con ty} (Γ : Usages γ) : (σs : Con ty) (Δ : Usages γ) → Set where
    ε   : Γ ⊢s ε s⊣ Γ
    _∙_ : {σs : Con ty} {σ : ty} {Δ E : Usages γ}
          (Ss : Γ ⊢s σs s⊣ Δ) (S : Δ ⊢ σ ⊣ E) →
          Γ ⊢s σs ∙ σ s⊣ E

injs[_] : (γ : Con ty) → Usages γ
injs[ γ ] = Context.induction {P = Usages} (λ a Γ → Γ ∙ [ a ]) ε γ

inj]_[ : (a : ty) → Cover a
inj] `κ k    [ = `κ k
inj] a `⊗ b  [ = inj] a [ `⊗ inj] b [
inj] a `& b  [ = a `& b
inj] a `⊸ b [ = ] a [`⊸ inj] b [

injs]_[ : (γ : Con ty) → Usages γ
injs] γ [ = Context.induction {P = Usages} (λ a Γ → Γ ∙ ] inj] a [ [) ε γ

isCoveredInj : (a : ty) → isCovered $ inj] a [
isCoveredInj (`κ k)    = `κ k
isCoveredInj (a `⊗ b)  = isCoveredInj a `⊗ isCoveredInj b
isCoveredInj (a `& b)  = a `& b
isCoveredInj (a `⊸ v) = ] a [`⊸ isCoveredInj v

isUsedInj : (a : ty) → isUsed $ ] inj] a [ [
isUsedInj a = ] isCoveredInj a [

_⊢_ : Con ty → ty → Set
Γ ⊢ a = injs[ Γ ] ⊢ a ⊣ injs] Γ [

test :
  let A = `κ 0
      B = `κ 1
  in ε ⊢ (A `⊸ B) `⊸ A `⊸ B
test =
  let A    = `κ 0
      B    = `κ 1
      f    :  _ → _ ⊢ B ⊣ _
      f xs = `κ[ suc (zro [ A `⊸ `κ 1 ]) ]$ xs
      x : _ ⊢ A ⊣ _
      x = `κ[ zro [ `κ 0 ] ]$ ε
  in isUsedInj (A `⊸ B) `⊸ ] `κ 0 [ `⊸ (f $ ε ∙ x)

S :
  let A = `κ 0
      B = `κ 1
      C = `κ 2
  in ε ⊢ (A `⊸ B `⊸ C) `⊸ (A `⊸ B) `⊸ (A `⊗ A) `⊸ C
S =
  let A      = `κ 0
      B      = `κ 1
      C      = `κ 2
-- projecting out the 2 values in the third argument
----------------------------------------------------
      x₁     : _ ⊢ A ⊣ _
      x₁     = `κ[ zro ] `κ 0 `⊗] `κ 0 [ [ ]$ ε
      x₂     : _ ⊢ A ⊣ _
      x₂     = `κ[ zro [ `κ 0 `⊗[ A ] ] ]$ ε
-- given an A, f will deliver a B
----------------------------------------------------
      f      : _ → _ ⊢ B ⊣ _
      f x    = `κ[ suc (zro [  A `⊸ `κ 1 ]) ]$ (ε ∙ x)
-- given an A and a B, g will deliver a C
----------------------------------------------------
      g      : _ → _ → _ ⊢ C ⊣ _
      g x fx = `κ[ suc (suc (zro [ A `⊸  B `⊸ `κ 2 ])) ]$ (ε ∙ fx ∙ x)
  in isUsedInj (A `⊸ B `⊸ C) `⊸
     isUsedInj (A `⊸ B)       `⊸
     isUsedInj (A `⊗ A)        `⊸
       g x₁ (f x₂)

swap :
  let A = `κ 0
      B = `κ 1
  in ε ⊢ A `⊗ B `⊸ B `⊗ A
swap =
  let A = `κ 0
      B = `κ 1
      b : _ ⊢ B ⊣ _
      b = `κ[ zro [ [ A ]`⊗ `κ 1 ] ]$ ε
      a : _ ⊢ A ⊣ _
      a = `κ[ zro ] ] `κ 0 [`⊗ `κ 1 [ ]$ ε
  in isUsedInj (A `⊗ B) `⊸ b `⊗ a

swap′ :
  let A  = `κ 0
      B₁ = `κ 1
      B₂ = `κ 2
  in ε ⊢ A `⊸ (A `⊸ B₁ `⊗ B₂) `⊸ B₂ `⊗ B₁
swap′ =
  let A    = `κ 0
      B₁   = `κ 1
      B₂   = `κ 2
-- assumption of type A
------------------------------
      a    : _ ⊢ A ⊣ _
      a    = `κ[ suc (zro [ `κ 0 ]) ]$ ε
-- the components one can extract
------------------------------
      b₁   : _ ⊢ B₁ ⊣ _
      b₁   = `κ[ zro ] ] A [`⊸ ] `κ 1 [`⊗ `κ 2 [ ]$ ε
      b₂   : _ → _ ⊢ B₂ ⊣ _
      b₂ a = `κ[ zro [  A `⊸ ([ B₁ ]`⊗ `κ 2) ] ]$ (ε ∙ a)
  in isUsedInj A `⊸
     isUsedInj (A `⊸ B₁ `⊗ B₂) `⊸
     b₂ a `⊗ b₁

