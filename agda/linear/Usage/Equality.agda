module linear.Usage.Equality where

open import Data.Nat
open import Data.Vec
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import linear.Type hiding (eq)
open import linear.Context
open import linear.Usage
open import linear.RawIso

eq : {a : Type} (A B : Usage a) → Dec (A ≡ B)
eq [ a ] [ .a ] = yes refl
eq ] a [ ] .a [ = yes refl
eq [ a ] ] .a [ = no (λ ())
eq ] a [ [ .a ] = no (λ ())

RawIso-∷ : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {a : Type} {A B : Usage a} →
           RawIso (A ≡ B × Γ ≡ Δ) ((Usages (a ∷ γ) ∋ A ∷ Γ) ≡ B ∷ Δ)
push RawIso-∷ (refl , refl) = refl
pull RawIso-∷ refl          = refl , refl

eqs : {n : ℕ} {γ : Context n} (Γ Δ : Usages γ) → Dec (Γ ≡ Δ)
eqs []      []      = yes refl
eqs (A ∷ Γ) (B ∷ Δ) = RawIso-∷ <$> eq A B <*> eqs Γ Δ
