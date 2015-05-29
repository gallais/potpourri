module lps.IMLLArr where

open import lib.Context
open import Data.Nat

open Context
open Context.Pointwise

open import Function
open import lib.Function


data ty : Set where
  `κ : ℕ → ty
  _`⊗_ _`&_ _`⊸_ : (σ τ : ty) → ty

infixr 30 _`⊗_ [_]`⊗_ _`&_ [_]`&_ [_]`⊸_ _`⊸_
infixl 30 _`⊗[_] _`&[_]
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
  [_]`⊸_ : (a : ty) {b : ty} (B : Cover b) → Cover $ a `⊸ b
  _`⊸_   : (a b : ty) → Cover $ a `⊸ b

data ]isUsed[ : {σ : ty} (S : Cover σ) → Set where
  `κ     : (k : ℕ) → ]isUsed[ $ `κ k
  _`⊗_   : {a b : ty} {A : Cover a} {B : Cover b} (prA : ]isUsed[ A) (prB : ]isUsed[ B) → ]isUsed[ $ A `⊗ B
  _`&_   : (a b : ty) → ]isUsed[ $ a `& b
  _`⊸_   : (a b : ty) → ]isUsed[ $ a `⊸ b

data Usage : ty → Set where
  [_] : (a : ty) → Usage a
  ]_[ : {a : ty} (A : Cover a) → Usage a

data isUsed {σ : ty} : (S : Usage σ) → Set where
  ]_[ : {S : Cover σ} (prS : ]isUsed[ S) → isUsed ] S [

Usages : Con ty → Set
Usages = PCon Usage

infix 4 [_]∋_∈_
data [_]∋_∈_ : (a : ty) (k : ℕ) (A : Cover a) → Set where
  `κ      : (k : ℕ) → [ `κ k ]∋ k ∈ `κ k
  _`&[_]  : {k : ℕ} {a : ty} {A : Cover a}
            (prA : [ a ]∋ k ∈ A ) (b : ty) → [ a `& b ]∋ k ∈ A `&[ b ] 
  [_]`&_  : {k : ℕ} (a : ty) {b : ty} {B : Cover b}
            (prB : [ b ]∋ k ∈ B ) → [ a `& b ]∋ k ∈ [ a ]`& B 
  _`⊗[_]  : {k : ℕ} {a : ty} {A : Cover a}
            (prA : [ a ]∋ k ∈ A ) (b : ty) → [ a `⊗ b ]∋ k ∈ A `⊗[ b ]
  [_]`⊗_  : {k : ℕ} (a : ty) {b : ty} {B : Cover b}
            (prB : [ b ]∋ k ∈ B) → [ a `⊗ b ]∋ k ∈ [ a ]`⊗ B
  _`⊸_    : {k : ℕ} (a : ty) {b : ty} {B : Cover b}
            (prB : [ b ]∋ k ∈ B) → [ a `⊸ b ]∋ k ∈ [ a ]`⊸ B

infix 4 ]_[∋_∈_
data ]_[∋_∈_ : {a : ty} (A : Cover a) (k : ℕ)
               (A′ : Cover a) → Set where
  [_]`⊗_ : {k : ℕ} (a : ty) {b : ty} {B B′ : Cover b} →
           ] B [∋ k ∈ B′ → ] [ a ]`⊗ B [∋ k ∈ [ a ]`⊗ B′
  _`⊗[_] : {k : ℕ} {a : ty} {A A′ : Cover a} →
           (prA : ] A [∋ k ∈ A′) (b : ty) → ] A `⊗[ b ] [∋ k ∈ A′ `⊗[ b ]
  _`⊗₂_  : {k : ℕ} {a b : ty} (A : Cover a) {B B′ : Cover b} →
           ] B [∋ k ∈ B′ → ] A `⊗ B [∋ k ∈ A `⊗ B′
  _`⊗₁_  : {k : ℕ} {a b : ty} {A A′ : Cover a} →
           (prA : ] A [∋ k ∈ A′) (B : Cover b) → ] A `⊗ B [∋ k ∈ A′ `⊗ B
  ]_[`⊗_ : {k : ℕ} {a b : ty} {A : Cover a} →
           (prA : [ a ]∋ k ∈ A) (B : Cover b) → ] [ a ]`⊗ B [∋ k ∈ A `⊗ B
  _`⊗]_[ : {k : ℕ} {a b : ty} (A : Cover a) {B : Cover b} →
           (prB : [ b ]∋ k ∈ B) → ] A `⊗[ b ] [∋ k ∈ A `⊗ B
  [_]`&_ : {k : ℕ} (a : ty) {b : ty} {B B′ : Cover b} →
           ] B [∋ k ∈ B′ → ] [ a ]`& B [∋ k ∈ [ a ]`& B′
  _`&[_] : {k : ℕ} {a : ty} {A A′ : Cover a} →
           (prA : ] A [∋ k ∈ A′) (b : ty) → ] A `&[ b ] [∋ k ∈ A′ `&[ b ]
  [_]`⊸_ : {k : ℕ} (a : ty) {b : ty} {B B′ : Cover b} (prB : ] B [∋ k ∈ B′) →
            ] [ a ]`⊸ B [∋ k ∈ [ a ]`⊸ B′

infix 4 _∋_∈_
infix 30 [_] ]_[
data _∋_∈_ {a : ty} : (A : Usage a) (k : ℕ)
           (A′ : Usage a) → Set where
  [_] : {A : Cover a} {k : ℕ} →
        [ a ]∋ k ∈ A → [ a ] ∋ k ∈ ] A [
  ]_[ : {A A′ : Cover a} {k : ℕ} →
        ] A [∋ k ∈ A′ → ] A [ ∋ k ∈ ] A′ [

infix 4 _∋s_s∈_
data _∋s_s∈_ : {γ : Con ty} (Γ : Usages γ) (k : ℕ)
               (Δ : Usages γ) → Set where
  zro : {γ : Con ty} {a : ty} {k : ℕ} {Γ : Usages γ} {A A′ : Usage a} →
        A ∋ k ∈ A′ → Γ ∙ A ∋s k s∈ Γ ∙ A′
  suc : {γ : Con ty} {a : ty} {k : ℕ} {Γ Δ : Usages γ} {A : Usage a} →
        Γ ∋s k s∈ Δ → Γ ∙ A ∋s k s∈ Δ ∙ A

infix 4 ]_[≡]_[⊙]_[
data ]_[≡]_[⊙]_[ : {σ : ty} (S S₁ S₂ : Cover σ) → Set where
  sym      : {a : ty} {A B C : Cover a} (pr : ] A [≡] B [⊙] C [) → ] A [≡] C [⊙] B [
  `κ       : (k : ℕ) → ] `κ k [≡] `κ k [⊙] `κ k [
  _`⊗_     : {a b : ty} {A A₁ A₂ : Cover a} {B B₁ B₂ : Cover b} →
             (prA : ] A [≡] A₁ [⊙] A₂ [) (prB : ] B [≡] B₁ [⊙] B₂ [) → 
             ] A `⊗ B [≡] A₁ `⊗ B₁ [⊙] A₂ `⊗ B₂ [
  [_]`⊗_   : {a : ty} {A A₁ A₂ : Cover a} (prA : ] A [≡] A₁ [⊙] A₂ [) (b : ty) →
             ] A `⊗[ b ] [≡] A₁ `⊗[ b ] [⊙] A₂ `⊗[ b ] [
  _`⊗[_]   : (a : ty) {b : ty} {B B₁ B₂ : Cover b} (prB : ] B [≡] B₁ [⊙] B₂ [) →
             ] [ a ]`⊗ B [≡] [ a ]`⊗ B₁ [⊙] [ a ]`⊗ B₂ [
  _`&_     : (a b : ty) → ] a `& b [≡] a `& b [⊙] a `& b [
  ]_[`&]_[ : {a b : ty} {A : Cover a} {B : Cover b}
             (prA : ]isUsed[ A) (prB : ]isUsed[ B) →
             ] a `& b [≡] A `&[ b ] [⊙] [ a ]`& B [
  ]_[`&    : {a b : ty} {B : Cover b} (prB : ]isUsed[ B) →
             ] a `& b [≡] [ a ]`& B [⊙] a `& b [
  _`&]_[   : {a b : ty} {A : Cover a} (prA : ]isUsed[ A) →
             ] a `& b [≡] A `&[ b ] [⊙] a `& b [
  _`&[_]   : {a : ty} {A A₁ A₂ : Cover a} (prA : ] A [≡] A₁ [⊙] A₂ [) (b : ty) →
             ] A `&[ b ] [≡] A₁ `&[ b ] [⊙] A₂ `&[ b ] [
  [_]`&_   : (a : ty) {b : ty} {B B₁ B₂ : Cover b} (prB : ] B [≡] B₁ [⊙] B₂ [) →
             ] [ a ]`& B [≡] [ a ]`& B₁ [⊙] [ a ]`& B₂ [
  [_]`⊸_   : (a : ty) {b : ty} {B B₁ B₂ : Cover b} (prB : ] B [≡] B₁ [⊙] B₂ [) →
             ] [ a ]`⊸ B [≡] [ a ]`⊸ B₁ [⊙] [ a ]`⊸ B₂ [
  _`⊸_     : (a b : ty) → ] a `⊸ b [≡] a `⊸ b [⊙] a `⊸ b [

infix 4 _≡_⊙_
infixl 20 _∙_
data _≡_⊙_ : {σ : ty} (S S₁ S₂ : Usage σ) → Set where
  [_] : (σ : ty) → [ σ ] ≡ [ σ ] ⊙ [ σ ]
  ]_[ : {σ : ty} {S S₁ S₂ : Cover σ} (pr : ] S [≡] S₁ [⊙] S₂ [) → ] S [ ≡ ] S₁ [ ⊙ ] S₂ [

infix 4 _s≡s_⊙_
data _s≡s_⊙_ : {γ : Con ty} (Γ Γ₁ Γ₂ : Usages γ) → Set where
  ε   : ε s≡s ε ⊙ ε 
  _∙_ : {γ : Con ty} {Γ Γ₁ Γ₂ : Usages γ} (prΓ : Γ s≡s Γ₁ ⊙ Γ₂)
        {σ : ty} {S S₁ S₂ : Usage σ} (prS : S ≡ S₁ ⊙ S₂) →
        Γ ∙ S s≡s Γ₁ ∙ S₁ ⊙ Γ₂ ∙ S₂

infix 4 ]_[cut_]_[
data ]_[cut_]_[ : {σ : ty} (S : Cover σ) (τ : ty) (T : Cover σ) → Set where
  -- actually performing a cut
  _`⊸_ : (σ : ty) {τ : ty} {T : Cover τ} (pr : ]isUsed[ T) → ] [ σ ]`⊸ T [cut σ ] σ `⊸ τ [
  -- structural rules
  [_]`⊗_ : {σ : ty} (a : ty) {b : ty} {B B′ : Cover b} →
           ] B [cut σ ] B′ [ → ] [ a ]`⊗ B [cut σ ] [ a ]`⊗ B′ [
  _`⊗[_] : {σ : ty} {a : ty} {A A′ : Cover a} →
           (prA : ] A [cut σ ] A′ [) (b : ty) → ] A `⊗[ b ] [cut σ ] A′ `⊗[ b ] [
  _`⊗₂_  : {σ : ty} {a b : ty} (A : Cover a) {B B′ : Cover b} →
           ] B [cut σ ] B′ [ → ] A `⊗ B [cut σ ] A `⊗ B′ [
  _`⊗₁_  : {σ : ty} {a b : ty} {A A′ : Cover a} →
           (prA : ] A [cut σ ] A′ [) (B : Cover b) → ] A `⊗ B [cut σ ] A′ `⊗ B [
  [_]`&_ : {σ : ty} (a : ty) {b : ty} {B B′ : Cover b} →
           ] B [cut σ ] B′ [ → ] [ a ]`& B [cut σ ] [ a ]`& B′ [
  _`&[_] : {σ : ty} {a : ty} {A A′ : Cover a} →
           (prA : ] A [cut σ ] A′ [) (b : ty) → ] A `&[ b ] [cut σ ] A′ `&[ b ] [
  [_]`⊸_ : {σ : ty} (a : ty) {b : ty} {B B′ : Cover b} (prB : ] B [cut σ ] B′ [) →
            ] [ a ]`⊸ B [cut σ ] [ a ]`⊸ B′ [

data cut {σ : ty} (τ : ty) : (S T : Usage σ) → Set where
  ]_[ : {S T : Cover σ} (pr : ] S [cut τ ] T [) → cut τ ] S [ ] T [

data cuts (τ : ty) : {γ : Con ty} (Γ Δ : Usages γ) → Set where
  zro : {γ : Con ty} {a : ty} {Γ : Usages γ} {A A′ : Usage a} →
        cut τ A A′ → cuts τ (Γ ∙ A) (Γ ∙ A′)
  suc : {γ : Con ty} {a : ty} {Γ Δ : Usages γ} {A : Usage a} →
        cuts τ Γ Δ → cuts τ (Γ ∙ A) (Δ ∙ A)

infix 4 _⊢_⊣_
infixr 5 _`&_by_ _thencut_by_ `λ_>_
data _⊢_⊣_ {γ : Con ty} (Γ : Usages γ) : (σ : ty) (Δ : Usages γ) → Set where
  `κ      : {k : ℕ} {Δ : Usages γ} (var : Γ ∋s k s∈ Δ) → Γ ⊢ `κ k ⊣ Δ
  _`⊗_    : {σ : ty} {Δ : Usages γ} (s : Γ ⊢ σ ⊣ Δ)
            {τ : ty} {E : Usages γ} (t : Δ ⊢ τ ⊣ E) → Γ ⊢ σ `⊗ τ ⊣ E
  _`&_by_ : {σ : ty} {Δ₁ : Usages γ} (s : Γ ⊢ σ ⊣ Δ₁)
            {τ : ty} {Δ₂ : Usages γ} (t : Γ ⊢ τ ⊣ Δ₂)
            {Δ : Usages γ} (pr : Δ s≡s Δ₁ ⊙ Δ₂)  → Γ ⊢ σ `& τ ⊣ Δ
  -- technically we'll always ever use cuts before closing the body
  -- of a lambda. this can be further refactored in the future.
  _thencut_by_ : {σ : ty} {Δ : Usages γ} (s : Γ ⊢ σ ⊣ Δ)
                 {χ : ty} {E : Usages γ} (pr : cuts χ Δ E)
                 {F : Usages γ} (c : E ⊢ χ ⊣ F) → Γ ⊢ σ ⊣ F
  `λ_>_    : {σ : ty} {S : Usage σ} (s : isUsed S)
            {τ : ty} {Δ : Usages γ} (t : Γ ∙ [ σ ] ⊢ τ ⊣ Δ ∙ S) → Γ ⊢ σ `⊸ τ ⊣ Δ

example :
  let A = `κ 0
      B = `κ 1
  in ε ⊢ (A `⊸ B) `⊸ A `⊸ B ⊣ ε
example =
  let A = `κ 0
      B = `κ 1
  in `λ ] A `⊸ B [ >
     `λ ] `κ 0 [   >
     let varA = `κ (zro [ `κ 0 ])
         varB = `κ (suc (zro [ A `⊸ `κ 1 ]))
         path = suc (zro ] A `⊸ `κ 1 [)
     in varB thencut path  by varA

S :
  let A = `κ 0
      B = `κ 1
      C = `κ 2
  in ε ⊢ (A `⊸ B `⊸ C) `⊸ (A `⊸ B) `⊸ (A `⊗ A) `⊸ C ⊣ ε
S =
  let A      = `κ 0
      B      = `κ 1
      C      = `κ 2
  in `λ ] A `⊸ B `⊸ C  [ >
     `λ ] A `⊸ B       [ >
     `λ ] `κ 0 `⊗ `κ 0 [ >
     let varC   = `κ (suc (suc (zro [ A `⊸ B `⊸ `κ 2 ])))
         pathB  = suc (suc (zro ] [ A ]`⊸ B `⊸ `κ 2 [))
         varB   = `κ (suc (zro [ A `⊸ `κ 1 ]))
         pathA₁ = suc (suc (zro ] A `⊸ B `⊸ C [))
         varA₁  = `κ (zro [ `κ 0 `⊗[ A ] ])
         pathA₂ = suc (zro ] A `⊸ `κ 1 [)
         varA₂  = `κ (zro ] `κ 0 `⊗] `κ 0 [ [)
     in varC  thencut pathB  by
        varB  thencut pathA₁ by
        varA₁ thencut pathA₂ by
        varA₂

apply : 
  let A = `κ 0
      B = `κ 1
      C = `κ 2
  in ε ⊢ ((A `⊸ B) `& (A `⊸ C)) `⊸ A `⊸ (B `& C) ⊣ ε
apply =
  let A      = `κ 0
      B      = `κ 1
      C      = `κ 2
  in `λ ] (A `⊸ B) `& (A `⊸ C) [ >
     `λ ] `κ zero              [ >
     let varB   = `κ (suc (zro [ (A `⊸ `κ 1) `&[ A `⊸ C ] ]))
         varC   = `κ (suc (zro [ [ A `⊸ B ]`& A `⊸ `κ 2 ]))
         pathAB = suc (zro ] (A `⊸ `κ 1) `&[ _ ] [)
         pathAC = suc (zro ] [ _ ]`& A `⊸ `κ 2 [)
         varAB  = `κ (zro [ `κ 0 ])
         varAC  = `κ (zro [ `κ 0 ])
         used   = ] ] A `⊸ B [`&] A `⊸ C [ [
     in (varB thencut pathAB by varAB)
     `& (varC thencut pathAC by varAC)
     by ε ∙ used ∙ ] `κ 0 [