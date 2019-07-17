module substsem.substsem where

open import Data.List.Base using (List; []; _∷_; [_])
open import Function
open import Relation.Unary using (_⊢_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)
open import Relation.Nary

data Type : Set where
  α    : Type
  _`→_ : (σ τ : Type) → Type

open import Data.List.Relation.Binary.Sublist.Propositional {A = Type} hiding (lookup)
open import Relation.Unary.Closure.Preorder ⊆-preorder as □

Scoped : Set₁
Scoped = Type → List Type → Set

variable
  σ τ : Type
  Γ Δ Θ : List Type
  C V W : Scoped

Var : Scoped
Var σ Γ = [ σ ] ⊆ Γ

th^Var : ∀ σ → Closed (Var σ)
Closed.next (th^Var _) = λ v th → ⊆-trans v th

data Tm : Scoped where
  `var : ∀[ Var ⇒ Tm ]
  `lam : ∀[ (σ ∷_) ⊢ Tm τ ⇒ Tm (σ `→ τ) ]
  `app : ∀[ Tm (σ `→ τ) ⇒ Tm σ ⇒ Tm τ ]

record _─Env (Γ : List Type) (V : Scoped) (Δ : List Type) : Set where
  constructor pack
  field lookup : Var σ Γ → V σ Δ
open _─Env

_─Env□ : ∀ Γ V Δ → Set
(Γ ─Env□) V Δ = (Γ ─Env) (□ ∘ V) Δ

map^Env : (∀ {σ} → V σ Δ → W σ Θ) → (Γ ─Env) V Δ → (Γ ─Env) W Θ
lookup (map^Env f ρ) k = f (lookup ρ k)

env□ :  (∀ σ → Closed (V σ)) → (Γ ─Env) V Δ → (Γ ─Env□) V Δ
env□ th^V = map^Env (Closed.next (th^V _))

th^Env : (∀ σ → Closed (V σ)) → Closed ((Γ ─Env) V)
Closed.next (th^Env th^V) ρ th = map^Env (λ v → Closed.next (th^V _) v th) ρ

th^Env□ : Closed ((Γ ─Env□) V)
th^Env□ = th^Env (λ σ → □-closed)

ε : ([] ─Env) V Δ
lookup ε ()

_∙_ : (Γ ─Env) V Δ → V σ Δ → ((σ ∷ Γ) ─Env) V Δ
lookup (ρ ∙ v) (refl ∷ _)  = v
lookup (ρ ∙ v) (_    ∷ʳ k) = lookup ρ k

record Sem (C : Scoped) : Set where
  field
    lam : ∀[ □ (□ (C σ) ⇒ C τ) ⇒ C (σ `→ τ) ]
    app : ∀[ C (σ `→ τ) ⇒ C σ ⇒ C τ ]

  sem : (Γ ─Env) (□ ∘ C) Δ → Tm σ Γ → C σ Δ
  sem ρ (`var k)   = extract $ lookup ρ k
  sem ρ (`lam b)   = lam (λ th v → sem (Closed.next th^Env□ ρ th ∙ v) b)
  sem ρ (`app f t) = app (sem ρ f) (sem ρ t)

var : ∀[ Var σ ⇒ □ (Tm σ) ]
var v th = `var (⊆-trans v th)

var₀ : □ (Tm σ) (σ ∷ Γ)
var₀ = var (refl ∷ minimum _)

bind : Γ ⊆ (σ ∷ Γ)
bind = _ ∷ʳ ⊆-refl

env : Γ ⊆ Δ → (Γ ─Env) Var Δ
env []        = ε
env (y ∷ʳ th) = Closed.next (th^Env th^Var) (env th) bind
env (x ∷ th)  = Closed.next (th^Env th^Var) (env th) bind ∙ (x ∷ minimum _)

sub : Sem Tm
Sem.lam sub = λ b → `lam (b bind var₀)
Sem.app sub = `app

th^Tm : ∀ σ → Closed (Tm σ)
Closed.next (th^Tm _) t th = Sem.sem sub ρ t where
  ρ = map^Env (□.map `var) $ env□ th^Var $ env th

_⟨_⟩ : Tm σ Γ → (Γ ─Env) Tm Δ → Tm σ Δ
t ⟨ ρ ⟩ = Sem.sem sub (env□ th^Tm ρ) t

Mod : Scoped
Mod α        Γ = Tm α Γ
Mod (σ `→ τ) Γ = □ (Mod σ ⇒ Mod τ) Γ

th^Mod : ∀ σ → Closed (Mod σ)
th^Mod α        = th^Tm α
th^Mod (σ `→ τ) = □-closed

mod : Sem Mod
Sem.lam mod = λ f th v → f th (Closed.next (th^Mod _) v)
Sem.app mod = extract

module _ (S : Sem C) where

  module S   = Sem S
  module Sub = Sem sub

  _⊚_ :  (Δ ─Env□) C Θ → (Γ ─Env□) Tm Δ → (Γ ─Env□) C Θ
  lookup (vs ⊚ ρ) k th = S.sem (Closed.next th^Env□ vs th) (lookup ρ k ⊆-refl)

  fusion : (t : Tm σ Γ) (ρ : (Γ ─Env□) Tm Δ) (vs : (Δ ─Env□) C Θ) →
           S.sem vs (Sub.sem ρ t) ≡ S.sem (vs ⊚ ρ) t
  fusion (`var k)   ρ vs = {!!}
  fusion (`lam b)   ρ vs = cong S.lam {!!}
  fusion (`app f t) ρ vs = cong₂ S.app (fusion f ρ vs) (fusion t ρ vs)
