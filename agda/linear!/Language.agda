module linear!.Language where

open import Agda.Builtin.Nat

-- Types: base, lolli & bang
data Type  : Set
data Type! : Set

infixr 4 _⊸_
data Type where
  `α    : Type
  _`⊸_ : Type! → Type! → Type

infix 6 _!^_
data Type! where
  _!^_ : Type → Nat → Type!

pattern α = `α !^ 0
pattern _⊸_ σ τ = σ `⊸ τ !^ 0

infixl 5 _!
_! : Type! → Type!
σ !^ n ! = σ !^ suc n

infixl 3 _:>_ _□
-- Contexts: (boxed) snoc-lists of types
data Context : Nat → Set where
  ε    : Context 0
  _:>_ : {n : Nat} → Context n → Type! → Context (suc n)
  _□   : {n : Nat} → Context n → Context n

-- Usage: fresh or stale
infix 4 fresh_ stale_
data Usage : Type! → Set where
  fresh_ : (σ : Type!) → Usage σ
  stale_ : (σ : Type!) → Usage σ

data Usages : {n : Nat} (γ : Context n) → Set where
  ε    : Usages ε
  _:>_ : {n : Nat} {γ : Context n} {σ : Type!} →
         Usages γ → Usage σ → Usages (γ :> σ)
  _□   : {n : Nat} {γ : Context n} →
         Usages γ → Usages (γ □)


open import Data.Fin
-- De Bruijn index as resource consumption
infix 1 _⊢var_∈_⊠_
infixr 5 op_ wk_
data _⊢var_∈_⊠_ : {n : Nat} {γ : Context n}
                  (Γ : Usages γ) (k : Fin n) (σ : Type!) (Δ : Usages γ) → Set where
  z!  : {n : Nat} {γ : Context n} {Γ : Usages γ} {σ : Type} {m p : Nat}
        {S : Usage (σ !^ suc m)} → Γ :> S ⊢var zero ∈ σ !^ p ⊠ Γ :> stale σ !^ suc m
  z0  : {n : Nat} {γ : Context n} {Γ : Usages γ} {σ : Type} →
        Γ :> (fresh σ !^ 0) ⊢var zero ∈ σ !^ 0 ⊠ Γ :> stale σ !^ 0
  wk_ : {n : Nat} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ} {σ τ : Type!} {S : Usage τ} →
        Γ ⊢var k ∈ σ ⊠ Δ → Γ :> S ⊢var suc k ∈ σ ⊠ Δ :> S

  op_ : {n : Nat} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ} {σ : Type!} →
        Γ ⊢var k ∈ σ ! ⊠ Δ → Γ □ ⊢var k ∈ σ ⊠ Δ □

_ : ε :> fresh α ! ! ! ! ⊢var _ ∈ α ⊠ _
_ = z!

_ : ε :> fresh α ! ! ! ! □ □ ⊢var _ ∈ α ⊠ _
_ = op op z!

_ : ε :> fresh α ! ! ! ! □ :> stale α □ ⊢var _ ∈ α ⊠ _
_ = op wk op z!

open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Product

z-constraint : {n : Nat} {γ : Context (suc n)} (Γ : Usages γ) → Nat → Set
z-constraint (Γ :> fresh σ !^ _)     zero    = ⊤
z-constraint (Γ :> fresh σ !^ suc _) (suc _) = ⊤
z-constraint (Γ :> stale σ !^ suc _) _       = ⊤
z-constraint (Γ :> _)                _       = ⊥
z-constraint (Γ □) m = z-constraint Γ (suc m)

z-constraint-valid :
  {n : Nat} {γ : Context (suc n)} (Γ : Usages γ) (m : Nat) →
  z-constraint Γ m → Type × Usages γ
z-constraint-valid (Γ :> fresh σ !^ k)     zero    pr = σ , (Γ :> stale σ !^ k)
z-constraint-valid (Γ :> fresh σ !^ suc k) (suc _) pr = σ , (Γ :> stale σ !^ suc k)
z-constraint-valid (Γ :> stale σ !^ suc k) _       pr = σ , (Γ :> stale σ !^ suc k)
z-constraint-valid (Γ □) m  pr = let (σ , Δ) = z-constraint-valid Γ (suc m) pr in (σ , (Δ □))
z-constraint-valid (Γ :> fresh σ !^ zero)  (suc _) ()
z-constraint-valid (Γ :> stale σ !^ zero)  _       ()

-- smart constructor for de Bruijn index 0
z : {n : Nat} {γ : Context (suc n)} {Γ : Usages γ}
    {m : Nat} {pr : z-constraint Γ m} →
    let (σ , Δ) = z-constraint-valid Γ m pr in
    Γ ⊢var zero ∈ σ !^ m ⊠ Δ
z {Γ = Γ :> fresh σ !^ zero}  {m = zero}  = z0
z {Γ = Γ :> fresh σ !^ suc k} {m = zero}  = z!
z {Γ = Γ :> fresh σ !^ suc k} {m = suc _} = z!
z {Γ = Γ :> stale σ !^ suc k}             = z!
z {Γ = Γ □} {m = m} = op z
z {Γ = Γ :> fresh σ !^ zero} {m = suc _} {pr = ()}
z {Γ = Γ :> stale σ !^ zero} {m = _}     {pr = ()}

_ : ε :> fresh α ! ! ! ! ⊢var _ ∈ α ⊠ _
_ = z

_ : ε :> fresh α ! ! ! ! □ □ ⊢var _ ∈ α ⊠ _
_ = z

_ : ε :> fresh α ! ! ! ! □ :> stale α □ ⊢var _ ∈ α ⊠ _
_ = op wk z

data Infer (n : Nat) : Set
data Check (n : Nat) : Set

data Infer n where
  var : Fin n → Infer n
  cut : Check n → Type! → Infer n
  app : Infer n → Check n → Infer n

data Check n where
  lam : Check (suc n) → Check n
  neu : Infer n → Check n

infix 1 _⊢_∋_⊠_ _⊢_∈_⊠_

data _⊢_∈_⊠_ {n : Nat} {γ : Context n} (Γ : Usages γ) :
             (t : Infer n) (σ : Type!) (Δ : Usages γ) → Set

data _⊢_∋_⊠_ {n : Nat} {γ : Context n} (Γ : Usages γ) :
             (σ : Type!) (t : Check n) (Δ : Usages γ) → Set

data _⊢_∈_⊠_ {n} {γ} Γ where

  var : {k : Fin n} {σ : Type!} {Δ : Usages γ} →
        Γ ⊢var k  ∈ σ ⊠ Δ →
        Γ ⊢ var k ∈ σ ⊠ Δ

  cut : {t : Check n} {σ : Type} {Δ : Usages γ} →
        Γ ⊢ σ !^ 0 ∋ t ⊠ Δ →
        Γ ⊢ cut t (σ !^ 0) ∈ σ !^ 0 ⊠ Δ

  app : {f : Infer n} {t : Check n} {σ τ : Type!} {Δ Θ : Usages γ} →
        Γ ⊢ f ∈ σ ⊸ τ ⊠ Δ → Δ ⊢ σ ∋ t ⊠ Θ →
        Γ ⊢ app f t ∈ τ ⊠ Θ

  box : {t : Infer n} {σ : Type} {m : Nat} {Δ : Usages γ} →
        Γ □ ⊢ t ∈ σ !^ 0     ⊠ Δ □ →
        Γ   ⊢ t ∈ σ !^ suc m ⊠ Δ

data _⊢_∋_⊠_ {n} {γ} Γ where

  lam : {b : Check (suc n)} {σ τ : Type!} {Δ : Usages γ} →
        Γ :> fresh σ ⊢      τ ∋     b ⊠ Δ :> stale σ →
        Γ            ⊢ σ ⊸ τ ∋ lam b ⊠ Δ

  box : {t : Check n} {σ : Type} {m : Nat} {Δ : Usages γ} →
        Γ □ ⊢ σ !^ 0     ∋ t ⊠ Δ □ →
        Γ   ⊢ σ !^ suc m ∋ t ⊠ Δ


  neu : {t : Infer n} {σ : Type} {Δ : Usages γ} →
        Γ ⊢ t ∈ σ !^ 0     ⊠ Δ →
        Γ ⊢ σ !^ 0 ∋ neu t ⊠ Δ

-- examples
_ : ε ⊢ (α ⊸ α) ! ∋ _ ⊠ ε
_ = box (lam (neu (var z)))

_ : ε ⊢ α ! ⊸ α ! ∋ _ ⊠ ε
_ = lam (box (neu (var z)))

_ : ε ⊢ α ! ⊸ α ! ! ! ! ∋ _ ⊠ ε
_ = lam (box (neu (var z)))
