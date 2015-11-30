module tt.red where

open import Data.Nat
open import Data.Product

open import tt.raw
open import tt.con
open import tt.env

infix 3 _[_⟩*_
data _[_⟩*_ {A : Set} (a : A) (R : A → A → Set) : (b : A) → Set where
  done  : a [ R ⟩* a
  more  : {b c : A} → R a b → b [ R ⟩* c → a [ R ⟩* c

mores : {A : Set} {a b c : A} {R : A → A → Set} → a [ R ⟩* b → b [ R ⟩* c → a [ R ⟩* c
mores done          red₂ = red₂
mores (more r red₁) red₂ = more r (mores red₁ red₂)

map[_,_,_,_,_,_⟩* : (A B : ℕ → Set) {m n : ℕ} (f : A m → B n)
            (R : IRel A) (S : IRel B) (F : {a a′ : A m} → R a a′ → S (f a) (f a′)) →
            {a a′ : A m} → a [ R ⟩* a′ → f a [ S ⟩* f a′
map[ A , B , f , R , S , F ⟩* done         = done
map[ A , B , f , R , S , F ⟩* (more r red) = more (F r) (map[ A , B , f , R , S , F ⟩* red)

wk[_,_⟩* : {A : ℕ → Set} {R : IRel A}
           (wk :  {m n : ℕ} (inc : m ⊆ n) → A m → A n)
           (wkR : {m n : ℕ} {a b : A m} (inc : m ⊆ n) → R a b → R (wk inc a) (wk inc b)) →
           {m n : ℕ} (inc : m ⊆ n) {a b : A m} → a [ R ⟩* b → wk inc a [ R ⟩* wk inc b
wk[_,_⟩* {A} {R} wk wkR inc = map[ A , A , wk inc , R , R , wkR inc ⟩*

record Syntax (E : ℕ → Set) : Set where
  eta-equality
  field
    weak  : Weakening E
    subst : Substituting Infer E

open Syntax public

record Reduction {E : ℕ → Set} (SE : Syntax E) (_↝_ : IRel E) : Set where
  module SE = Syntax SE
  field
    weak↝       : {m n : ℕ} {a b : E m} (inc : m ⊆ n) → a ↝ b → SE.weak inc a ↝ SE.weak inc b
    subst↝      : {m n : ℕ} {a b : E m} (ρ : Var m =>[ Infer ] n) → a ↝ b → SE.subst a ρ ↝ SE.subst b ρ
    confluence  : {m : ℕ} {a b c : E m} → a [ _↝_ ⟩* b → a [ _↝_ ⟩* c →
                  ∃ λ d → b [ _↝_ ⟩* d × c [ _↝_ ⟩* d

record WeakHead (f : Type ⇒ Type) (_↝_ : IRel Type) : Set where
  field
    yieldsWhnf   : {n : ℕ} (t : Type n) → Type f t ≡^Con f t
    yieldsReduct : {n : ℕ} (t : Type n) → t [ _↝_ ⟩* f t
    uncoversHead : {n : ℕ} (t : Type n) (ex : ∃ λ s → (t [ _↝_ ⟩* s) × Type s ≡^Con s) →
                   Type f t ≡^Con proj₁ ex
