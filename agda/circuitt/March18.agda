module circuitt.March18 where

open import Function

data Phase : Set where
  CT ML : Phase

infixr 5 _⇒_
data Type : Set where
  𝟚   : Phase → Type
  _⇒_ : (σ τ : Type) → Type

infixl 5 _∙_
data Ctx : Set where
  ε   : Ctx
  _∙_ : Ctx → Type → Ctx

open import Relation.Unary renaming (_⇒_ to _⟶_)

data Var : Type → Ctx → Set where
  z : ∀ {σ}   → ∀[         (_∙ σ) ⊢ Var σ ]
  s : ∀ {τ σ} → ∀[ Var σ ⟶ (_∙ τ) ⊢ Var σ ]

data Lang : Type → Ctx → Set where
  var : ∀ {σ}   → ∀[ Var σ ⟶ Lang σ ]
  app : ∀ {σ τ} → ∀[ Lang (σ ⇒ τ) ⟶ (Lang σ ⟶ Lang τ) ]
  lam : ∀ {σ τ} → ∀[ (_∙ σ) ⊢ Lang τ ⟶ Lang (σ ⇒ τ) ]

open import Data.Bool
open import Data.Nat.Base
open import Data.Fin

size : Ctx → ℕ
size ε          = 0
size (Γ ∙ 𝟚 CT) = suc (size Γ)
size (Γ ∙ σ)    = size Γ

data Circuit : ℕ → Set where
  fin : ∀[ Fin ⟶ Circuit ]

Val : Type → Ctx → Set
Val (𝟚 CT)  = Circuit ∘ size
Val (𝟚 ML)  = const Bool
Val (σ ⇒ τ) = Val σ ⟶ Val τ

infix 4 _─Env
record _─Env (Γ : Ctx) (V : Type → Ctx → Set) (Δ : Ctx) : Set where
  constructor pack
  field lookup : ∀ {σ} → Var σ Γ → V σ Δ
open _─Env public

_∙^E_ : ∀ {Γ Δ V σ} → (Γ ─Env) V Δ → V σ Δ → (Γ ∙ σ ─Env) V Δ
lookup (ρ ∙^E v) (z _)   = v
lookup (ρ ∙^E v) (s _ k) = lookup ρ k

sem : ∀ {σ Γ Δ} → Lang σ Γ → (Γ ─Env) Val Δ → Val σ Δ
sem (var _ v)   ρ = lookup ρ v
sem (app _ f t) ρ = sem f ρ (sem t ρ)
sem (lam _ b)   ρ = λ v → sem b (ρ ∙^E v)

𝟚s : ℕ → Ctx
𝟚s zero    = ε
𝟚s (suc n) = 𝟚s n ∙ 𝟚 CT

open import Relation.Binary.PropositionalEquality

size-𝟚s : ∀ {n} → size (𝟚s n) ≡ n
size-𝟚s {zero}  = refl
size-𝟚s {suc n} = cong suc size-𝟚s

open import Data.Product

fromVar : ∀ n {σ} → Var σ (𝟚s n) → Val σ (𝟚s n) × σ ≡ 𝟚 CT
fromVar zero ()
fromVar (suc n) (z _)   = fin _ zero , refl
fromVar (suc n) (s _ v) with fromVar n v
... | fin _ k , refl = fin _ (suc k) , refl

eval : ∀ {n} → Lang (𝟚 CT) (𝟚s n) → Circuit n
eval t = subst Circuit size-𝟚s (sem t (pack (proj₁ ∘ (fromVar _))))
