-- This is what Peter Hancock showed us today.
-- Obviously, all mistakes are mine.

-- Nat's definition requires an impredicative universe...
{-# OPTIONS --type-in-type #-}

module lenses where

open import Data.Unit
open import Data.Sum
open import Data.Product as Product
open import Function

FNat : Set → Set
FNat X = ⊤ ⊎ X

record Lens : Set where
  constructor _∙_∙_
  field
-- A Lens is given by: the [L]ens type transformer,
-- and a pair of an [U]p and a [D]own function.
    L : Set → Set
    U : (X : Set) (alg : FNat X → X) → FNat (L X) → L X
    D : (X : Set) (alg : FNat X → X) → L X → X

-- Usual Church encoding of Nat
Nat : Set
Nat = (X : Set) (s : X → X) (z : X) → X

zero : Nat
zero = λ X s z → z

succ : Nat → Nat
succ n = λ X s → s ∘ n X s

-- From a Lens, one can always extract a function
-- from Nat to Nat
eval : Lens → Nat → Nat
eval l n = Lens.D l Nat alg $ n (Lens.L l Nat) (Lens.U l Nat alg ∘ inj₂) (Lens.U l Nat alg $ inj₁ tt)
  where
    alg : FNat Nat → Nat
    alg = [ const zero , succ ]

-- Addition of a constant is a simple enough Lens
_+ : Nat → Lens
n + =
  let L X        = X
      U X alg    = [ const (n X (alg ∘ inj₂) (alg $ inj₁ tt)) , alg ∘ inj₂ ]
      D X alg lx = lx
  in L ∙ U ∙ D

-- Predecessor is slightly more complicated
-- (we follow the usual trick)
pred : Lens
pred =
  let L X        = X × X
      U X alg    =
        let `0 = alg $ inj₁ tt
            `s = alg ∘ inj₂
        in [ const (`0 , `0) , (uncurry λ p _ → `s p , p) ]
      D X alg lx = proj₂ lx
  in L ∙ U ∙ D

-- Exponentiation requires (L X) to be a function space!
_^ : Nat → Lens
n ^ =
  let L X        = X → X
      U X alg    = [ const $ alg ∘ inj₂ , n X ]
      D X alg lx = lx $ alg $ inj₁ tt
  in L ∙ U ∙ D


infixr 5 _^^_ _++_
_++_ : Nat → Nat → Nat
m ++ n = eval (m +) n

_^^_ : Nat → Nat → Nat
m ^^ n = eval (m ^) n


-- A few examples showing that it indeed works as expected:

Nat32 : Nat
Nat32 = `2 ^^ succ (`2 ++ `2)
  where `2 = succ (succ zero)

Nat31 : Nat
Nat31 = eval pred Nat32

open import Data.List as List
open import Data.Nat as ℕ using (ℕ)

ℕify : Nat → ℕ
ℕify n = n ℕ ℕ.suc 0

test : List ℕ
test = List.map ℕify $ Nat32 ∷ Nat31 ∷ []
