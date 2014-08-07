module MultiSigma where

open import Data.Product as Prod using (_,_)

prod prod' : (A : Set) (B : A → Set) → Set
prod A  B = Prod.Σ A B
prod' A B = Prod.Σ A B

Σ[_ : Set → Set
Σ[_ A = A

syntax prod  A (λ a → B) = a ∶ A ] B
syntax prod' A (λ a → B) = a ∶ A ∣ B

infix  3 prod
infixr 2 prod'
infix  1 Σ[_

postulate
  N   : Set
  K   : Set → Set
  kn  : K N
  _∈_ : (n : N) (ns : K N) → Set
  P   : ∀ n (pr : n ∈ kn) → Set

elt : Σ[ n ∶ N ∣ n∈ ∶ n ∈ kn ∣ pr ∶ P n n∈ ] N
elt = {!!} , {!!} , {!!} , {!!}