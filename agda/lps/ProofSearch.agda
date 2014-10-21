module lps.ProofSearch where

open import Data.Empty
open import Data.Unit
open import Data.Product as Prod
open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import lib.Nullary
open import lib.Context          as Con
import lps.IMLL                  as IMLL
import lps.Equivalence           as Equivalence


module Prove (Pr : Set) (_≟_ : (x y : Pr) → Dec (x ≡ y)) where

  open IMLL Pr
  open Con.Context
  open IMLL.Type Pr
  open Equivalence Pr _≟_

  prove : (Γ : Con ty) (σ : ty) {_ : dec (⊢-dec Γ σ) (const ⊤) (const ⊥)}→ Γ ⊢ σ
  prove Γ σ {pr} = tactics (uncurry ⊢-dec) (Γ , σ) {pr}