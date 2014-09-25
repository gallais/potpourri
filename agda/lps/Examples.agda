open import lib.Context          as Con
import lps.IMLL                  as IMLL

module lps.Examples where

  open import Data.Nat

  open Con.Context
  open IMLL ℕ
  open IMLL.Type ℕ
  open import lps.ProofSearch
  open Prove ℕ _≟_

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