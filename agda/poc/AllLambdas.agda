module poc.AllLambdas where

open import Data.Unit.Base

record Parameters : Set₁ where
  field Ctx  : Set
        Bnd  : Set
        Var  : Ctx → Set
        _,-_ : Ctx → Bnd → Ctx

module Syntax (P : Parameters) where

  open Parameters P

  data Lam (Γ : Ctx) : Set where
    `var : Var Γ → Lam Γ
    `app : Lam Γ → Lam Γ → Lam Γ
    `lam : (b : Bnd) → Lam (Γ ,- b) → Lam Γ

module Raw where

  open import Data.String.Base

  p : Parameters
  p = record
    { Ctx  = ⊤
    ; Bnd  = String
    ; Var  = λ _ → String
    ; _,-_ = _
    }

  module Raw = Syntax.Lam p
  Raw = Syntax.Lam p

  pattern `λ_↦_ str b = Syntax.`lam str b


module Scoped where

  open import Data.Nat.Base
  open import Data.Fin.Base

  p : Parameters
  p = record
    { Ctx  = ℕ
    ; Bnd  = ⊤
    ; Var  = Fin
    ; _,-_ = λ n _ → suc n
    }

  module Scoped = Syntax.Lam p
  Scoped = Syntax.Lam p

  pattern `λ b = Syntax.`lam _ b
