module lps.ProofSearch where

open import Data.Empty
open import Data.Unit
open import Data.Product as Prod
open import Function

open import lib.Nullary
open import lib.Maybe            as Maybe
open import lib.Context          as Con
import lps.IMLL                  as IMLL
import lps.Linearity             as Linearity
import lps.Linearity.Consumption as Consumption
import lps.Search.Calculus       as Calculus


module Prove where

  open IMLL
  open Con.Context
  open IMLL.Type
  open Linearity
  open Linearity.Context
  open Calculus
  open Calculus.Calculus

  check : {γ : Con ty} {σ : ty} (Δ : Usage γ) (prf : inj[ γ ] ⊢ σ ⊣ Δ) →
          Maybe $ γ ⊢ σ
  check Δ prf =
    let (E , d , tm) = Soundness.Context.⟦ prf ⟧
    in dec (LC.isUsed? E) (some ∘ flip ⟦isUsed⟧ tm) (const none)

  search : (Γ : Con ty) (σ : ty) → Maybe $ Γ ⊢ σ
  search Γ σ = Context.foldl (Maybe.app ∘ uncurry check) none $ inj[ Γ ] ⊢? σ

  prove : (Γ : Con ty) (σ : ty) {_ : maybe (const ⊤) ⊥ $ search Γ σ} → Γ ⊢ σ
  prove Γ σ {pr} = Maybe.induction P ⊥-elim const (search Γ σ) pr
    where P = λ a → ∀ (pr : maybe (const ⊤) ⊥ a) → Γ ⊢ σ

module Examples where

  open Con.Context
  open IMLL
  open IMLL.Type
  open Prove

  example⊗ :
    let A = `κ 0
        γ = ε ∙ A `⊗ A
    in γ ⊢ A `⊗ A
  example⊗ = prove _ _

  example& :
    let A = `κ 0
        γ = ε ∙ (A `& (A `⊗ A))
    in γ ⊢ A
  example& = prove _ _

  example&′ :
    let A = `κ 0
        B = `κ 1
        φ = (A `& B) `& B
        γ = ε ∙ φ
    in γ ⊢ φ
  example&′ = prove _ _