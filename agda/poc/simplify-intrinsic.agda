open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Product.Base using (Σ-syntax; _,_; proj₁)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; module ≡-Reasoning)
open import Relation.Unary using (IUniversal)

data Ty : Set where
  `nat `bool : Ty

variable
  ty : Ty

⟦_⟧ty : Ty → Set
⟦ `nat  ⟧ty = ℕ
⟦ `bool ⟧ty = Bool

data Expr : Ty → Set where
  `lit : ⟦ ty ⟧ty → Expr ty
  `add : (m n : Expr `nat) → Expr `nat
  `mul : (m n : Expr `nat) → Expr `nat

⟦_⟧ : Expr ty → ⟦ ty ⟧ty
⟦ `lit l   ⟧ = l
⟦ `add m n ⟧ = ⟦ m ⟧ + ⟦ n ⟧
⟦ `mul m n ⟧ = ⟦ m ⟧ * ⟦ n ⟧

Rule : Ty → Set
Rule ty = (e : Expr ty) → Σ[ r ∈ Expr ty ] ⟦ e ⟧ ≡ ⟦ r ⟧

infixr 0 _then_

_then_ : Rule ty → Rule ty → Rule ty
(f then g) t
  = let open ≡-Reasoning in
    let (r₁ , prf₁) = f t in
    let (r₂ , prf₂) = g r₁ in
    (r₂ ,_) $ begin
      ⟦ t  ⟧ ≡⟨ prf₁ ⟩
      ⟦ r₁ ⟧ ≡⟨ prf₂ ⟩
      ⟦ r₂ ⟧ ∎

{-# INLINE _then_ #-}

simplify : ∀[ Rule ] → ∀[ Rule ]
simplify f = fgo module Simplify where

  fgo : ∀[ Rule ]
  go : ∀[ Rule ]

  open ≡-Reasoning

  fgo = go then f

  go (`lit l) = `lit l , refl
  go (`add m n)
    = let (rm , prfm) = fgo m in
      let (rn , prfn) = fgo n in
      (`add rm rn) , cong₂ _+_ prfm prfn
  go (`mul m n)
    = let (rm , prfm) = fgo m in
      let (rn , prfn) = fgo n in
      (`mul rm rn) , cong₂ _*_ prfm prfn

0+ : ∀[ Rule ]
0+ (`add (`lit 0) n) = n , refl
0+ t = t , refl

0* : ∀[ Rule ]
0* (`mul (`lit 0) n) = `lit 0 , refl
0* t = t , refl


cleanup : ∀[ Rule ]
cleanup = simplify (0* then 0+)

_ : ∀ {a b} → proj₁ (cleanup (`add (`mul (`lit 0) (`lit a)) (`lit b))) ≡ (`lit b)
_ = refl
