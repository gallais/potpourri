
-- Proving a goal in ILL
--------------------------------------------------
-- This is the primary use of our solver: automatically produce
-- derivations in ILL when presented with a problem.
-- We use natural numbers as names for our atomic propositions.
-- The solver finds all possible proofs but we only retain the
-- first one.

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



--------------------------------------------------
-- Solving equations on a commutative monoid
--------------------------------------------------
-- We have derived a solver for equations on a commutative monoid
-- from a restriction of our solver for ILL based on ILLWiL. Here
-- is an example of it in action on an equation involving natural
-- numbers.
-- We use the standard library's proof that (ℕ, 0, _+_, ≡) is
-- indeed a commutative monoid.


  open import Algebra.Structures
  open import Data.Nat as Nat
  open import Data.Nat.Properties
  module AbSR = IsCommutativeSemiring isCommutativeSemiring

  import Relation.Binary.PropositionalEquality as RBEq

  open import Data.Fin as Fin hiding (_+_)
  open import Data.Vec as Vec
  open import lps.Tactics
  module ℕ+ = TacticsAbMon (record
                        { Carrier = ℕ
                        ; _≈_ = RBEq._≡_
                        ; _∙_ = _+_
                        ; ε   = 0
                        ; isCommutativeMonoid = AbSR.+-isCommutativeMonoid
                        }) Nat._≟_
  import Prelude as Pr

  2+x+y+1 : (x y : Nat.ℕ) → 2 + (x + y + 1) RBEq.≡ x + 3 + y
  2+x+y+1 x y =
     let open ℕ+
         `x  = `v Fin.zero
         `y  = `v (Fin.suc Fin.zero)
         LHS = `c 2 `∙ ((`x `∙ `y) `∙ `c 1)
         RHS = (`x `∙ `c 3) `∙ `y
     in proveMonEq LHS RHS (x Vec.∷ y Vec.∷ Vec.[])



--------------------------------------------------
-- Proving two lists to be bag-equivalent
--------------------------------------------------
-- Last but not least, we can leverage the solver for commutative
-- monoids to automatically discharge proofs goals stating that
-- two given lists are bag equivalent (as defined by Nils Anders
-- Danielsson in his 2012 ITP paper).


  open import Bag-equivalence
  module BE = BagEq Nat.ℕ Nat._≟_

  sgl : ℕ → Pr.List ℕ
  sgl x = x Pr.∷ Pr.[]

  1∷2∷3∷3′ : let open Pr in
             (xs : List Nat.ℕ) →
             1 ∷ 2 ∷ 3 ∷ xs Pr.++ 3 ∷ [] ≈-bag 3 ∷ 2 ∷ xs Pr.++ 3 ∷ 1 ∷ []
  1∷2∷3∷3′ xs = BE.proveMonEq LHS RHS CTX
    where open BE
          `1  = `v Fin.zero
          `2  = `v (Fin.suc Fin.zero)
          `3  = `v (Fin.suc (Fin.suc Fin.zero))
          `xs = `v (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
          LHS = ((`1 `∙ `2 `∙ `3) `∙ `xs) `∙ `3
          RHS = (`3 `∙ `2) `∙ `xs `∙ `3 `∙ `1
          CTX = sgl 1 Vec.∷ sgl 2 Vec.∷ sgl 3 Vec.∷ xs Vec.∷ Vec.[]
