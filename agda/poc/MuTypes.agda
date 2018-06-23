module poc.MuTypes where

open import Size
open import Data.Unit
open import Data.Product
open import Data.Fin
open import Data.Maybe as Maybe hiding (All)
open import Data.List as List
open import Function

open import Data.List.Any
open import Data.List.Membership.Propositional

data Type (i : Size) : Set where
  _`→_ : (σ τ : Type i) → Type i
  `μ   : ∀ {j : Size< i} → List (List (Maybe (Type j))) → Type i

args : List (Maybe Set) → Set → Set
args []      X = ⊤
args (x ∷ c) X = maybe id X x × args c X

data mu (cs : List (List (Maybe Set))) : Set where
  con : (k : Fin (length cs)) → args (lookup cs k) (mu cs) → mu cs

type  : ∀ {i} → Type i → Set
type (σ `→ τ) = type σ → type τ
type (`μ cs)  = mu (List.map (List.map (Maybe.map type)) cs)

nat : Type _
nat = `μ ([] ∷ (nothing ∷ []) ∷ [])

list : Type _ → Type _
list a = `μ ([] ∷ (just a ∷ nothing ∷ []) ∷ [])

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

pattern z   = con zero tt
pattern s n = con (suc zero) (n , tt)

fromNat : Nat → type nat
fromNat zero    = z
fromNat (suc n) = s (fromNat n)

toNat : type nat → Nat
toNat z     = zero
toNat (s n) = suc (toNat n)
toNat (con (suc (suc ())) _)
