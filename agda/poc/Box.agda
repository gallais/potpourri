module poc.Box where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Function hiding (id)
open import Relation.Binary.PropositionalEquality

Circuit : Set₁
Circuit = ℕ → ℕ → Set

_⨄_ : Circuit → Circuit → Circuit
(c ⨄ d) m n = c m n ⊎ d m n

_⟶_ : Circuit → Circuit → Set
c ⟶ d = ∀ {m n} → c m n → d m n


data C (c : Circuit) : Circuit where
  sub  : c ⟶ C c
  id   : ∀ {m} → C c m m
  swp  : C c 2 2
  grd  : ∀ {m} → C c m 0
  dup  : C c 1 2
  src  : Bool → C c 0 1
  _||_ : ∀ {m n p q} → C c m n → C c p q → C c (m + p) (n + q)
  _>>_ : ∀ {m n p} → C c m n → C c n p → C c m p

data Box (t : Circuit) (c : Circuit) : Circuit where
  reify   : t ⟶ Box t c
  circuit : C (Box t c ⨄ c) ⟶ Box t c

module _ (g : Circuit) where

  Srcs : Circuit
  Srcs m n = m ≡ 0 × (Fin n → Bool)

  srcs : ∀ n → C g 0 n
  srcs zero    = id
  srcs (suc n) = src true || srcs n

  evalBox : Box Srcs g ⟶ C g
  evalC   : C (Box Srcs g ⨄ g) ⟶ C g
  evalFin : ∀ m → (Fin m → Bool) → C g 0 m

  evalBox (reify f)   rewrite proj₁ f
                      = evalFin _ $ proj₂ f
  evalBox (circuit c) = evalC c

  evalC (sub (inj₁ b)) = evalBox b
  evalC (sub (inj₂ c)) = sub c
  evalC id             = id
  evalC swp            = swp
  evalC grd            = grd
  evalC dup            = dup
  evalC (src b)        = src b
  evalC (c || d)       = evalC c || evalC d
  evalC (c >> d)       = evalC c >> evalC d

  evalFin zero    f = id
  evalFin (suc m) f = src (f zero) || evalFin m (f ∘ suc)
