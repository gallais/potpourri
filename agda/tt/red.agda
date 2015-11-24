module tt.red where

open import Data.Nat

Red : (E : ℕ → Set) → Set₁
Red E = {n : ℕ} (e f : E n) → Set

infix 3 _[_⟩*_

data _[_⟩*_ {A : Set} (a : A) (R : A → A → Set) : (b : A) → Set where
  done  : a [ R ⟩* a
  more  : {b c : A} → R a b → b [ R ⟩* c → a [ R ⟩* c
