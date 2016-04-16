module linear.Typecheck.Examples where

open import linear.Type
open import linear.Language
open import linear.Language.Examples
open import linear.Usage
open import linear.Typing
open import linear.Typing.Examples
open import linear.Typecheck
open import linear.Typecheck.Problem

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

swapChecked : {σ τ : Type} → check [] ((σ ⊗ τ) ─o (τ ⊗ σ)) swap ≡ yes ([] , swapTyped)
swapChecked {σ} {τ} rewrite eq-diag τ | eq-diag σ = refl

identityInfer : {σ : Type} → --let σ = κ 0 ⊗ κ 1 in
                infer [] (`cut identity (σ ─o σ)) ≡ yes (σ ─o σ , [] , `cut identityTyped)
identityInfer {σ} rewrite eq-diag σ = refl
