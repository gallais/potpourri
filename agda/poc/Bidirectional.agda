module poc.Bidirectional where

open import Data.Empty
open import Data.Unit
open import Data.List hiding ([_])
open import Function

data Ty : Set where
  ⋆    : Ty
  _`→_ : Ty → Ty → Ty

Cx = List Ty
Model = Ty → Cx → Set

infix 3 [_]
infixr 5 _⟶_
infix 7 _⊢_

[_] : (Cx → Set) → Set
[ T ] = ∀ {Γ} → T Γ

_⟶_ : (Cx → Set) → (Cx → Set) → (Cx → Set)
(S ⟶ T) Γ = S Γ → T Γ

_⊢_ : Ty → (Cx → Set) → (Cx → Set)
(σ ⊢ T) Γ = T (σ ∷ Γ)

data Var : Model where
  `z : ∀ {σ} → [ σ ⊢ Var σ ]
  `s : ∀ {σ τ} → [ Var σ ⟶ τ ⊢ Var σ ]

infix 4 _─Env
record _─Env (Γ : Cx) (V : Model) (Δ : Cx) : Set where
  constructor pack
  field lookup : ∀ {σ} → Var σ Γ → V σ Δ
open _─Env

infixr 5 _∙_
_∙_ : ∀ {Γ V σ} → [ (Γ ─Env) V ⟶ V σ ⟶ (σ ∷ Γ ─Env) V ]
lookup (ρ ∙ v) `z     = v
lookup (ρ ∙ v) (`s k) = lookup ρ k

Thinning : Cx → Cx → Set
Thinning Γ Δ = (Γ ─Env) Var Δ

refl : ∀ {Γ} → Thinning Γ Γ
refl = pack id

extend : ∀ {Γ σ} → Thinning Γ (σ ∷ Γ)
extend = pack `s

select : ∀ {Γ Δ Θ V} → Thinning Γ Δ → (Δ ─Env) V Θ → (Γ ─Env) V Θ
lookup (select ρ ρ′) k = lookup ρ′ (lookup ρ k)

Thinnable : (Cx → Set) → Set
Thinnable T = ∀ {Γ Δ} → Thinning Γ Δ → (T Γ → T Δ)

record Thinnable′ (T : Model) : Set where
  constructor mkThinnable′
  field th′ : ∀ {σ} → Thinnable (T σ)
open Thinnable′

thVar : Thinnable′ Var
th′ thVar ren k = lookup ren k

thEnv : ∀ {Γ V} → (Thinnable′ V) → Thinnable ((Γ ─Env) V)
lookup (thEnv thV ren ρ) k = th′ thV ren (lookup ρ k)

□ : (Cx → Set) → (Cx → Set)
(□ S) Γ = ∀ {Δ} → Thinning Γ Δ → S Δ

th□ : ∀ {T} → Thinnable (□ T)
th□ ρ t ρ′ = t (select ρ ρ′)

record Mode : Set₁ where
  field
    CUT : Ty → Set
    THK : Ty → Set

module Terms (M : Mode) where

  open Mode M

  mutual

    data Thk : Model where
      `var : ∀ {σ}         → [ Var σ                ⟶ Thk σ ]
      `app : ∀ {σ τ}       → [ Thk (σ `→ τ) ⟶ Val σ ⟶ Thk τ ]
      `cut : ∀ {σ} → CUT σ → [ Val σ                ⟶ Thk σ ]

    data Val : Model where
      `lam : ∀ {σ τ}         → [ σ ⊢ Val τ ⟶ Val (σ `→ τ) ]
      `thk : ∀ {σ}   → THK σ → [ Thk σ     ⟶ Val σ        ]

-- I wish this worked:
-- open import Data.Product
-- (Infer , Check) : Model × Model
-- (Infer , Check) = let open Terms Syntax in (Thk , Val)

Syntax : Mode
Mode.CUT Syntax = const ⊤
Mode.THK Syntax = const ⊤

Infer = let open Terms Syntax in Thk
Check = let open Terms Syntax in Val

Value : Mode
Mode.CUT Value = const ⊥
Mode.THK Value = λ { ⋆ → ⊤; _ → ⊥ }

isStar : Ty → Set
isStar = λ { ⋆ → ⊤; _ → ⊥ }

Neutral = let open Terms Value in Thk
Normal  = let open Terms Value in Val

record Evaluator (M : Mode) (E : Model) (T : Model) (V : Model) : Set where
  open Mode M
  field
    thV : Thinnable′ E
    -- Thk
    var : ∀ {σ}         → [ E σ              ⟶ T σ        ]
    app : ∀ {σ τ}       → [ T (σ `→ τ) ⟶ V σ ⟶ T τ        ]
    cut : ∀ {σ} → CUT σ → [ V σ              ⟶ T σ        ]
    -- Val
    lam : ∀ {σ τ}       → [ □ (E σ ⟶  V τ)   ⟶ V (σ `→ τ) ]
    thk : ∀ {σ} → THK σ → [ T σ              ⟶ V σ        ]

module Eval {M E T V} (𝓔 : Evaluator M E T V) where

  open Terms M
  open Evaluator 𝓔

  Semantics : Model → Model → Set
  Semantics Tm Mo = ∀ {σ Γ Δ} → (Γ ─Env) E Δ → Tm σ Γ → Mo σ Δ

  semT : Semantics Thk T
  semV : Semantics Val V

  semT ρ (`var k)    = var (lookup ρ k)
  semT ρ (`app t v)  = app (semT ρ t) (semV ρ v)
  semT ρ (`cut pr v) = cut pr (semV ρ v)

  semV ρ (`lam v)    = lam (λ ren arg → semV (thEnv thV ren ρ ∙ arg) v)
  semV ρ (`thk pr t) = thk pr (semT ρ t)

module Syntactic (M : Mode) where

  open Terms M

  REN : Evaluator M Var Thk Val
  Evaluator.thV REN = thVar
  Evaluator.var REN = `var
  Evaluator.app REN = `app
  Evaluator.cut REN = `cut
  Evaluator.lam REN = λ b → `lam (b extend `z)
  Evaluator.thk REN = `thk

  thThk : Thinnable′ Thk
  thThk = mkThinnable′ $ Eval.semT REN
  thVal : Thinnable′ Val
  thVal = mkThinnable′ $ Eval.semV REN

  SUB : Evaluator M Thk Thk Val
  Evaluator.thV SUB = thThk
  Evaluator.var SUB = id
  Evaluator.app SUB = `app
  Evaluator.cut SUB = `cut
  Evaluator.lam SUB = λ b → `lam (b extend (`var `z))
  Evaluator.thk SUB = `thk

Kr : Model
Kr ⋆        = Neutral ⋆
Kr (σ `→ τ) = □ (Kr σ ⟶ Kr τ)

thKr : Thinnable′ Kr
th′ thKr {⋆}      = th′ (Syntactic.thThk Value)
th′ thKr {σ `→ τ} = th□

NBE : ∀ {M} → Evaluator M Kr Kr Kr
Evaluator.thV NBE = thKr
Evaluator.var NBE = id
Evaluator.app NBE = (_$ refl)
Evaluator.cut NBE = λ _ → id
Evaluator.lam NBE = id
Evaluator.thk NBE = λ _ → id

reify   : (σ : Ty) → [ Kr σ      ⟶ Normal σ ]
reflect : (σ : Ty) → [ Neutral σ ⟶ Kr σ     ]

reify ⋆        n = Terms.`thk tt n
reify (σ `→ τ) f = let body = f extend (reflect σ (Terms.`var `z))
                   in Terms.`lam (reify τ body)

reflect ⋆        n = n
reflect (σ `→ τ) n = λ ren v →
                     let fun = th′ (Syntactic.thThk Value) ren n
                         arg = reify σ v
                     in reflect τ (Terms.`app fun arg)

normThk : ∀ {R σ} → [ Terms.Thk R σ ⟶ Normal σ ]
normThk = reify _ ∘ Eval.semT NBE (pack (reflect _ ∘ Terms.`var))

normVal : ∀ {R σ} → [ Terms.Val R σ ⟶ Normal σ ]
normVal = reify _ ∘ Eval.semV NBE (pack (reflect _ ∘ Terms.`var))


normInfer   : ∀ {σ} → [ Infer σ   ⟶ Normal σ ]
normCheck   : ∀ {σ} → [ Check σ   ⟶ Normal σ ]
normNeutral : ∀ {σ} → [ Neutral σ ⟶ Normal σ ]
normNormal  : ∀ {σ} → [ Normal σ  ⟶ Normal σ ]

normInfer   = normThk
normCheck   = normVal
normNeutral = normThk
normNormal  = normVal
