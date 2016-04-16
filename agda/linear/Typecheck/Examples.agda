module linear.Typecheck.Examples where

open import linear.Type
open import linear.Language
open import linear.Language.Examples
open import linear.Usage
open import linear.Typing.Examples
open import linear.Typecheck
open import linear.Typecheck.Problem

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

swapChecked : let σ = κ 1; τ = κ 2 in check [] ((σ ⊗ τ) ─o (τ ⊗ σ)) swap ≡ yes ([] , swapTyped)
swapChecked = refl
