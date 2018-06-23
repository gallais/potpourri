module poc.MuTypes where

open import Size
open import Data.Unit
open import Data.Product
open import Data.Maybe as Maybe hiding (All)
open import Data.List as List
open import Data.List.All

open import Data.List.Any
open import Data.List.Membership.Propositional

data Type : Set where
  _`→_ : (σ τ : Type) → Type
  `μ   : List (List (Maybe Type)) → Type

type  : Type → Set
data mu (cs : List (List (Maybe Type))) : Set

type (σ `→ τ) = type σ → type τ
type (`μ cs)  = mu cs

data mu cs where
  con : ∀ {c} → c ∈ cs → All (maybe type (mu cs)) c → mu cs


{-
nat : Type
nat = `μ ([] ∷ (nothing ∷ []) ∷ [])

list : Type → Type
list a = `μ ([] ∷ (just a ∷ nothing ∷ []) ∷ [])

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

pattern z   = con (here refl) tt
pattern s n = con (there (here refl)) (n , tt)

fromNat : Nat → type nat
fromNat zero    = z
fromNat (suc n) = s (fromNat n)

toNat : type nat → Nat
toNat z     = zero
toNat (s n) = suc (toNat n)
toNat (con (there (there ())) _)
-}
