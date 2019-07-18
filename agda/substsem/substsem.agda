open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

module substsem.substsem
       (ext : Extensionality 0ℓ 0ℓ)
       (iext : ExtensionalityImplicit 0ℓ 0ℓ)
       where

open import Data.List.Base using (List; []; _∷_; [_])
open import Function
open import Function.Nary.NonDependent
open import Relation.Unary using (_⊢_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans-reflʳ; trans-assoc; module ≡-Reasoning)
open import Relation.Nary

data Type : Set where
  α    : Type
  _`→_ : (σ τ : Type) → Type

open import Data.List.Relation.Binary.Sublist.Propositional {A = Type} hiding (lookup)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties {A = Type}
open import Relation.Unary.Closure.Preorder ⊆-preorder as □

Scoped : Set₁
Scoped = Type → List Type → Set

variable
  σ τ : Type
  Γ Δ Θ Ω : List Type
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

zero : Var σ (σ ∷ Γ)
zero = refl ∷ minimum _

var₀ : Tm σ (σ ∷ Γ)
var₀ = `var zero

□var₀ : □ (Tm σ) (σ ∷ Γ)
□var₀ = var zero

bind : Γ ⊆ (σ ∷ Γ)
bind = _ ∷ʳ ⊆-refl

toRen : Γ ⊆ Δ → (Γ ─Env) Var Δ
toRen []        = ε
toRen (y ∷ʳ th) = Closed.next (th^Env th^Var) (toRen th) bind
toRen (x ∷ th)  = Closed.next (th^Env th^Var) (toRen th) bind ∙ (x ∷ minimum _)

toRen□ : Γ ⊆ Δ → (Γ ─Env□) Var Δ
toRen□ th = env□ th^Var $ toRen th

toSub : Γ ⊆ Δ → (Γ ─Env□) Tm Δ
toSub th = map^Env (□.map `var) (toRen□ th)

sub : Sem Tm
Sem.lam sub = λ b → `lam (b bind □var₀)
Sem.app sub = `app

th^Tm : ∀ σ → Closed (Tm σ)
Closed.next (th^Tm _) t th = Sem.sem sub (toSub th) t

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

record All (Γ : List Type) {V W : Scoped} (R : ∀[ V ⇒ W ⇒ constₙ 2 Set ]) {Δ}
           (vs : (Γ ─Env) V Δ) (ws : (Γ ─Env) W Δ) : Set where
  constructor pack^R
  field lookup^R : (k : Var σ Γ) → R (lookup vs k) (lookup ws k)
open All

⊆-trans-reflʳ : (th : Γ ⊆ Δ) → ⊆-trans th ⊆-refl ≡ th
⊆-trans-reflʳ []        = refl
⊆-trans-reflʳ (y ∷ʳ th) = cong (y ∷ʳ_) (⊆-trans-reflʳ th)
⊆-trans-reflʳ (x ∷ th)  = cong₂ _∷_ (trans-reflʳ x) (⊆-trans-reflʳ th)

⊆-trans-reflˡ : (th : Γ ⊆ Δ) → ⊆-trans ⊆-refl th ≡ th
⊆-trans-reflˡ {[]}    th        = []⊆-irrelevant (⊆-trans ⊆-refl th) th
⊆-trans-reflˡ {σ ∷ Γ} (eq ∷ th) = cong (eq ∷_) (⊆-trans-reflˡ th)
⊆-trans-reflˡ {σ ∷ Γ} (y ∷ʳ th) = cong (y ∷ʳ_) (⊆-trans-reflˡ th)

⊆-trans-assoc : (th₀ : Γ ⊆ Δ) (th₁ : Δ ⊆ Θ) (th₂ : Θ ⊆ Ω) →
  ⊆-trans (⊆-trans th₀ th₁) th₂ ≡ ⊆-trans th₀ (⊆-trans th₁ th₂)
⊆-trans-assoc []         th₁ th₂ = []⊆-irrelevant _ _
⊆-trans-assoc (x ∷ʳ th₀) (y ∷ʳ th₁) (z ∷ʳ th₂)  =
  cong (z ∷ʳ_) (⊆-trans-assoc (x ∷ʳ th₀) (y ∷ʳ th₁) th₂)
⊆-trans-assoc (x ∷ʳ th₀) (y ∷ʳ th₁) (eqz ∷ th₂) =
  cong (_ ∷ʳ_) (⊆-trans-assoc (x ∷ʳ th₀) th₁ th₂)
⊆-trans-assoc (x ∷ʳ th₀) (eqy ∷ th₁) (z ∷ʳ th₂) =
  cong (z ∷ʳ_) (⊆-trans-assoc (x ∷ʳ th₀) (eqy ∷ th₁) th₂)
⊆-trans-assoc (x ∷ʳ th₀) (eqy ∷ th₁) (eqz ∷ th₂) =
  cong (_ ∷ʳ_) (⊆-trans-assoc th₀ th₁ th₂)
⊆-trans-assoc (eqx ∷ th₀) (y ∷ʳ th₁) (z ∷ʳ th₂) =
  cong (z ∷ʳ_) (⊆-trans-assoc (eqx ∷ th₀) (y ∷ʳ th₁) th₂)
⊆-trans-assoc (eqx ∷ th₀) (y ∷ʳ th₁) (eqz ∷ th₂) =
  cong (_ ∷ʳ_) (⊆-trans-assoc (eqx ∷ th₀) th₁ th₂)
⊆-trans-assoc (eqx ∷ th₀) (eqy ∷ th₁) (z ∷ʳ th₂) =
  cong (z ∷ʳ_) (⊆-trans-assoc (eqx ∷ th₀) (eqy ∷ th₁) th₂)
⊆-trans-assoc (eqx ∷ th₀) (eqy ∷ th₁) (eqz ∷ th₂) =
  cong₂ _∷_ (trans-assoc eqx) (⊆-trans-assoc th₀ th₁ th₂)

-- infixr 5 _∷_ _∷ʳ_

⊆-trans-bindʳ : (th : Γ ⊆ Δ) → ⊆-trans th bind ≡ σ ∷ʳ th
⊆-trans-bindʳ []         = refl
⊆-trans-bindʳ (y ∷ʳ th)  = cong (λ th → _ ∷ʳ y ∷ʳ th) (⊆-trans-reflʳ th)
⊆-trans-bindʳ th@(_ ∷ _) = cong (_ ∷ʳ_) (⊆-trans-reflʳ th)


next-refl-id : (vs : (Γ ─Env□) V Δ) → All Γ _≡_ vs (Closed.next th^Env□ vs ⊆-refl)
lookup^R (next-refl-id vs) k = iext $ ext $ λ th →
  cong (lookup vs k) (sym $ ⊆-trans-reflˡ th)

lookup-toRen : (th : Γ ⊆ Δ) (k : Var σ Γ) → lookup (toRen th) k ≡ ⊆-trans k th
lookup-toRen (y ∷ʳ th) k = begin
  lookup (toRen (y ∷ʳ th)) k         ≡⟨⟩
  ⊆-trans (lookup (toRen th) k) bind ≡⟨ cong (λ t → ⊆-trans t bind) (lookup-toRen th k) ⟩
  ⊆-trans (⊆-trans k th) bind        ≡⟨ ⊆-trans-assoc k th bind ⟩
  ⊆-trans k (⊆-trans th bind)        ≡⟨ cong (⊆-trans k) (⊆-trans-bindʳ th) ⟩
  ⊆-trans k (y ∷ʳ th)                ∎ where open ≡-Reasoning
lookup-toRen (eqx ∷ th) (y ∷ʳ k)  = begin
  lookup (toRen (eqx ∷ th)) (y ∷ʳ k) ≡⟨⟩
  ⊆-trans (lookup (toRen th) k) bind ≡⟨ ⊆-trans-bindʳ (lookup (toRen th) k) ⟩
  _ ∷ʳ lookup (toRen th) k           ≡⟨ cong (_ ∷ʳ_) (lookup-toRen th k) ⟩
  _ ∷ʳ ⊆-trans k th                  ≡⟨⟩
  ⊆-trans (y ∷ʳ k) (eqx ∷ th)        ∎ where open ≡-Reasoning
lookup-toRen (eqx ∷ th) (refl ∷ k) = cong (eqx ∷_) ([]⊆-irrelevant _ _)


next-toSub : (th : Γ ⊆ Δ) →
  All (σ ∷ Γ) _≡_ (Closed.next th^Env□ (toSub th) bind ∙ □var₀) (toSub (refl ∷ th))
lookup^R (next-toSub th) (refl ∷ k) = refl
lookup^R (next-toSub th) (y ∷ʳ k)   = iext $ ext $ λ th′ →
  cong `var $ sym $ ⊆-trans-assoc (lookup (toRen th) k) bind th′

lookup-toSub : (th : Γ ⊆ Δ) (k : Var σ Γ) (th′ : Δ ⊆ Θ) →
               lookup (toSub th) k th′ ≡ `var (⊆-trans k (⊆-trans th th′))
lookup-toSub th k th′ = begin
  lookup (toSub th) k th′
    ≡⟨⟩
  `var (⊆-trans (lookup (toRen th) k) th′)
    ≡⟨ cong (λ th → `var (⊆-trans th th′)) (lookup-toRen th k) ⟩
  `var (⊆-trans (⊆-trans k th) th′)
    ≡⟨ cong `var (⊆-trans-assoc k th th′) ⟩
  `var (⊆-trans k (⊆-trans th th′))
    ∎ where open ≡-Reasoning

sub-id : (t : Tm σ Γ) (ρ : (Γ ─Env□) Tm Γ) →
         All Γ _≡_ ρ (toSub ⊆-refl) → Sem.sem sub ρ t ≡ t
sub-id (`var k)   ρ ρ^R = begin
  Sem.sem sub ρ (`var k)
    ≡⟨⟩
  lookup ρ k ⊆-refl
    ≡⟨ cong extract (lookup^R ρ^R k) ⟩
  lookup (toSub ⊆-refl) k ⊆-refl
    ≡⟨ lookup-toSub ⊆-refl k ⊆-refl ⟩
  `var (⊆-trans k (⊆-trans ⊆-refl ⊆-refl))
    ≡⟨ cong (λ th → `var (⊆-trans k th)) (⊆-trans-reflʳ ⊆-refl) ⟩
  `var (⊆-trans k ⊆-refl)
    ≡⟨ cong `var (⊆-trans-reflʳ k) ⟩
  `var k
    ∎ where open ≡-Reasoning
sub-id (`app f t) ρ ρ^R = cong₂ `app (sub-id f ρ ρ^R) (sub-id t ρ ρ^R)
sub-id (`lam b)   ρ ρ^R = cong `lam $
  sub-id b (Closed.next th^Env□ ρ bind ∙ □var₀) $ pack^R λ where
    (refl ∷ _) → refl
    (_ ∷ʳ k)   → iext $ ext $ λ th → begin
      lookup (Closed.next th^Env□ ρ bind) k th
        ≡⟨⟩
      lookup ρ k (⊆-trans bind th)
        ≡⟨ cong (λ f → f (⊆-trans bind th)) (lookup^R ρ^R k) ⟩
      lookup (toSub ⊆-refl) k (⊆-trans bind th)
        ≡⟨ lookup-toSub ⊆-refl k (⊆-trans bind th) ⟩
      `var (⊆-trans k (⊆-trans ⊆-refl (⊆-trans bind th)))
        ≡⟨ cong (λ th → `var (⊆-trans k th)) (⊆-trans-reflˡ _) ⟩
      `var (⊆-trans k (⊆-trans bind th))
        ≡⟨ cong `var (sym $ ⊆-trans-assoc k bind th) ⟩
      `var (⊆-trans (⊆-trans k bind) th)
        ≡⟨ cong (λ k → `var (⊆-trans k th)) (⊆-trans-bindʳ k) ⟩
      `var (⊆-trans (_ ∷ʳ k) th)
        ≡⟨ cong (λ th → `var (⊆-trans (_ ∷ʳ k) th)) (sym $ ⊆-trans-reflˡ th) ⟩
      `var (⊆-trans (_ ∷ʳ k) (⊆-trans ⊆-refl th))
        ≡⟨ sym $ lookup-toSub ⊆-refl (_ ∷ʳ k) th ⟩
      lookup (toSub ⊆-refl) (_ ∷ʳ k) th
        ∎ where open ≡-Reasoning

module _ (S : Sem C) where

  private
    module S = Sem S

  extensional : (t : Tm σ Γ) (vs ws : (Γ ─Env□) C Δ) →
                All Γ _≡_ vs ws → S.sem vs t ≡ S.sem ws t
  extensional (`var k)   vs ws rel = cong extract (lookup^R rel k)
  extensional (`lam b)   vs ws rel = cong S.lam $ iext $ ext $ λ th → ext $ λ v →
    let vs′ = Closed.next th^Env□ vs th ∙ (λ th → v th)
        ws′ = Closed.next th^Env□ ws th ∙ (λ th → v th)
    in extensional b vs′ ws′ $ pack^R $ λ where
         (refl ∷ _)  → refl
         (_    ∷ʳ k) → iext $ ext $ λ th′ → cong (λ f → f (⊆-trans th th′)) (lookup^R rel k)
  extensional (`app f t) vs ws rel =
    cong₂ S.app (extensional f vs ws rel) (extensional t vs ws rel)


_⊚_ :  (Δ ─Env□) C Θ → Γ ⊆ Δ → (Γ ─Env□) C Θ
lookup (vs ⊚ th) k = lookup vs (⊆-trans k th)

module _ (S : Sem C) where

  private
    module S   = Sem S
    module Sub = Sem sub

  ren-fusion : (t : Tm σ Γ) (th : Γ ⊆ Δ) (vs : (Δ ─Env□) C Θ) (ws : (Γ ─Env□) C Θ) →
               All Γ _≡_ (vs ⊚ th) ws → S.sem vs (Sub.sem (toSub th) t) ≡ S.sem ws t
  ren-fusion (`var k)   th vs ws rel = begin
    S.sem vs (Sub.sem (toSub th) (`var k))
      ≡⟨⟩
    lookup vs (⊆-trans (lookup (toRen th) k) ⊆-refl) ⊆-refl
      ≡⟨ cong (λ k → lookup vs k ⊆-refl) (⊆-trans-reflʳ _) ⟩
    lookup vs (lookup (toRen th) k) ⊆-refl
      ≡⟨ cong (λ k → lookup vs k ⊆-refl) (lookup-toRen th k) ⟩
    lookup vs (⊆-trans k th) ⊆-refl
      ≡⟨ cong extract (lookup^R rel k) ⟩
    lookup ws k ⊆-refl
      ≡⟨⟩
    S.sem ws (`var k)
      ∎ where open ≡-Reasoning
  ren-fusion (`app f t) th vs ws rel =
    cong₂ S.app (ren-fusion f th vs ws rel) (ren-fusion t th vs ws rel)
  ren-fusion {σ `→ τ} (`lam b) re vs ws rel =
    cong S.lam $ iext $ λ {Ω} → ext $ λ th → ext $ λ v → body Ω th (λ th → v th) where

    body : ∀ Ω (th : _ ⊆ Ω) (v : □ (C σ) Ω) →
           S.sem _ (Sub.sem _ b) ≡ S.sem _ b
    body Ω th v = begin
      S.sem vs′ (Sub.sem re′₀ b)
        ≡⟨ cong (S.sem vs′) (extensional sub b re′₀ (toSub (refl ∷ re)) (next-toSub re)) ⟩
      S.sem vs′ (Sub.sem (toSub (refl ∷ re)) b)
        ≡⟨ ren-fusion b (refl ∷ re) vs′ ws′ env-eq ⟩
      S.sem ws′ b
      ∎ where

      open ≡-Reasoning
      vs′  = Closed.next th^Env□ vs th ∙ v
      re′  = Closed.next th^Env□ (toSub re) bind
      re′₀ = re′ ∙ □var₀
      ws′  = Closed.next th^Env□ ws th ∙ v

      env-eq : All (σ ∷ _) _≡_ (vs′ ⊚ (refl ∷ re)) ws′
      lookup^R env-eq (refl ∷ k) = refl
      lookup^R env-eq (y ∷ʳ k)   = iext $ ext $ λ th′ →
        cong (λ f → f (⊆-trans th th′)) (lookup^R rel k)

ren-ren : (t : Tm σ Γ) (th₀ : Γ ⊆ Δ) (th₁ : Δ ⊆ Θ) (th₂ : Γ ⊆ Θ) →
          ⊆-trans th₀ th₁ ≡ th₂ →
          Sem.sem sub (toSub th₁) (Sem.sem sub (toSub th₀) t) ≡ Sem.sem sub (toSub th₂) t
ren-ren (`var k)   th₀ th₁ th₂ rel = cong `var $ begin
  ⊆-trans (lookup (toRen th₁) (⊆-trans (lookup (toRen th₀) k) ⊆-refl)) ⊆-refl
    ≡⟨ ⊆-trans-reflʳ _ ⟩
  lookup (toRen th₁) (⊆-trans (lookup (toRen th₀) k) ⊆-refl)
    ≡⟨ cong (lookup (toRen th₁)) (⊆-trans-reflʳ _) ⟩
  lookup (toRen th₁) (lookup (toRen th₀) k)
    ≡⟨ lookup-toRen th₁ (lookup (toRen th₀) k) ⟩
  ⊆-trans (lookup (toRen th₀) k) th₁
    ≡⟨ cong (flip ⊆-trans th₁) (lookup-toRen th₀ k) ⟩
  ⊆-trans (⊆-trans k th₀) th₁
    ≡⟨ ⊆-trans-assoc k th₀ th₁ ⟩
  ⊆-trans k (⊆-trans th₀ th₁)
    ≡⟨ cong (⊆-trans k) rel ⟩
  ⊆-trans k th₂
    ≡⟨ sym $ lookup-toRen th₂ k ⟩
  lookup (toRen th₂) k
    ≡⟨ sym $ ⊆-trans-reflʳ _ ⟩
  ⊆-trans (lookup (toRen th₂) k) ⊆-refl ∎ where open ≡-Reasoning
ren-ren (`app f t) th₀ th₁ th₂ rel =
  cong₂ `app (ren-ren f th₀ th₁ th₂ rel) (ren-ren t th₀ th₁ th₂ rel)
ren-ren (`lam b) th₀ th₁ th₂ rel = cong `lam $
  let th₀′ = Closed.next th^Env□ (toSub th₀) bind ∙ □var₀
      th₁′ = Closed.next th^Env□ (toSub th₁) bind ∙ □var₀
      th₂′ = Closed.next th^Env□ (toSub th₂) bind ∙ □var₀
  in begin
  Sem.sem sub th₁′ (Sem.sem sub th₀′ b)
    ≡⟨ extensional sub (Sem.sem sub th₀′ b) th₁′ (toSub (refl ∷ th₁)) (next-toSub th₁) ⟩
  Sem.sem sub (toSub (refl ∷ th₁)) (Sem.sem sub th₀′ b)
    ≡⟨ cong (Sem.sem sub _) (extensional sub b th₀′ (toSub (refl ∷ th₀)) (next-toSub th₀)) ⟩
  Sem.sem sub (toSub (refl ∷ th₁)) (Sem.sem sub (toSub (refl ∷ th₀)) b)
    ≡⟨ ren-ren b (refl ∷ th₀) (refl ∷ th₁) (refl ∷ th₂) (cong (refl ∷_) rel) ⟩
  Sem.sem sub (toSub (refl ∷ th₂)) b
    ≡⟨ sym $ extensional sub b th₂′ (toSub (refl ∷ th₂)) (next-toSub th₂) ⟩
  Sem.sem sub th₂′ b
    ∎ where open ≡-Reasoning


module _ (S : Sem C) where

  private
    module S   = Sem S
    module Sub = Sem sub

  _⊚′_ :  (Δ ─Env□) C Θ → (Γ ─Env) Tm Δ → (Γ ─Env□) C Θ
  lookup (vs ⊚′ ρ) k th = S.sem (Closed.next th^Env□ vs th) (lookup ρ k)

  `var-subst : (v : Var σ Γ) (ρ : (Γ ─Env) Tm Δ) →
               `var v ⟨ ρ ⟩ ≡ lookup ρ v
  `var-subst k ρ = sub-id (lookup ρ k) (toSub ⊆-refl) (pack^R (λ _ → refl))

  fusion : (t : Tm σ Γ) (ρ : (Γ ─Env) Tm Δ) (vs : (Δ ─Env□) C Θ) (vs∘ρ : (Γ ─Env□) C Θ) →
           All Γ _≡_ (vs ⊚′ ρ) vs∘ρ → S.sem vs (t ⟨ ρ ⟩) ≡ S.sem vs∘ρ t
  fusion (`var v)   ρ vs vs∘ρ rel = begin
    S.sem vs (`var v ⟨ ρ ⟩)
      ≡⟨ cong (S.sem vs) (`var-subst v ρ) ⟩
    S.sem vs (lookup ρ v)
      ≡⟨ extensional S (lookup ρ v) vs (Closed.next th^Env□ vs ⊆-refl) (next-refl-id vs) ⟩
    S.sem (Closed.next th^Env□ vs ⊆-refl) (lookup ρ v)
      ≡⟨ cong extract (lookup^R rel v) ⟩
    extract (lookup vs∘ρ v)
      ≡⟨⟩
    S.sem vs∘ρ (`var v)
      ∎ where open ≡-Reasoning
  fusion (`app f t) ρ vs vs∘ρ rel =
    cong₂ S.app (fusion f ρ vs vs∘ρ rel) (fusion t ρ vs vs∘ρ rel)
  fusion {σ `→ τ} (`lam b)   ρ vs vs∘ρ ρ^R =
    cong S.lam $ iext $ λ {Ω} → ext $ λ th → ext $ λ v → body Ω th (λ th → v th) where

    body : ∀ Ω (th : _ ⊆ Ω) (v : □ (C σ) Ω) →
          S.sem _ (Sub.sem _ b) ≡ S.sem _ b
    body Ω th v = begin
      S.sem vs′ (Sub.sem □ρ′₀ b)
        ≡⟨ cong (S.sem vs′) (extensional sub b □ρ′₀ (env□ th^Tm ρ′₀) sub-eq) ⟩
      S.sem vs′ (b ⟨ ρ′₀ ⟩)
        ≡⟨ fusion b ρ′₀ vs′ vs∘ρ′₀ env-eq ⟩
      S.sem vs∘ρ′₀ b
        ∎ where

      open ≡-Reasoning
      □ρ′₀   = Closed.next th^Env□ (env□ th^Tm ρ) bind ∙ □var₀
      ρ′₀    = Closed.next (th^Env th^Tm) ρ bind ∙ var₀
      vs′    = Closed.next th^Env□ vs th ∙ v
      vs∘ρ′₀ = Closed.next th^Env□ vs∘ρ th ∙ v

      sub-eq : All (σ ∷ _) _≡_ □ρ′₀ (env□ th^Tm ρ′₀)
      lookup^R sub-eq k@(refl ∷ _) = iext $ ext $ λ th′ → begin
        lookup □ρ′₀ k th′
          ≡⟨⟩
        `var (⊆-trans zero th′)
          ≡⟨ cong `var (sym $ lookup-toRen th′ zero) ⟩
        `var (lookup (toRen th′) zero)
          ≡⟨ cong `var (sym $ ⊆-trans-reflʳ _) ⟩
        `var (⊆-trans (lookup (toRen th′) zero) ⊆-refl)
          ≡⟨⟩
        lookup (env□ th^Tm ρ′₀) k th′ ∎
      lookup^R sub-eq (_ ∷ʳ k) = iext $ ext $ λ th′ → begin
        lookup □ρ′₀ (σ ∷ʳ k) th′
          ≡⟨⟩
        lookup (Closed.next th^Env□ (env□ th^Tm ρ) bind) k th′
          ≡⟨⟩
        duplicate (lookup (env□ th^Tm ρ) k) bind th′
          ≡⟨⟩
        duplicate (λ th → Sem.sem sub (toSub th) (lookup ρ k)) bind th′
          ≡⟨⟩
        Sem.sem sub (toSub (⊆-trans bind th′)) (lookup ρ k)
          ≡⟨ sym $ ren-ren (lookup ρ k) bind th′ (⊆-trans bind th′) refl ⟩
        Sem.sem sub (toSub th′) (Sem.sem sub (toSub bind) (lookup ρ k))
          ≡⟨⟩
        Sem.sem sub (toSub th′) (lookup (Closed.next (th^Env th^Tm) ρ bind) k)
          ≡⟨⟩
        lookup (env□ th^Tm $ Closed.next (th^Env th^Tm) ρ bind) k th′
          ≡⟨⟩
        lookup (env□ th^Tm ρ′₀) (σ ∷ʳ k) th′
          ∎

      env-eq : All (σ ∷ _) _≡_ (vs′ ⊚′ ρ′₀) vs∘ρ′₀
      lookup^R env-eq (refl ∷ k) = iext $ ext $ λ th → cong v (⊆-trans-reflʳ th)
      lookup^R env-eq (y ∷ʳ k)   = iext $ λ {Ξ} → ext $ λ th′ → step-case Ξ th′ where

        step-case : ∀ Ξ (th′ : Ω ⊆ Ξ) →
          lookup (vs′ ⊚′ ρ′₀) (σ ∷ʳ k) th′
           ≡ lookup vs∘ρ′₀ (σ ∷ʳ k) th′
        step-case Ξ th′ = begin
          lookup (vs′ ⊚′ ρ′₀) (σ ∷ʳ k) th′
            ≡⟨⟩
          S.sem vs′′ (lookup ρ′₀ (σ ∷ʳ k))
            ≡⟨⟩
          S.sem vs′′ (lookup (Closed.next (th^Env th^Tm) ρ bind) k)
            ≡⟨⟩
          S.sem vs′′ (Sem.sem sub (toSub bind) (lookup ρ k))
            ≡⟨ ren-fusion S (lookup ρ k) bind vs′′ vs″ vs-eq ⟩
          S.sem vs″ (lookup ρ k)
            ≡⟨⟩
          lookup (vs ⊚′ ρ) k (⊆-trans th th′)
            ≡⟨ cong (λ f → f (⊆-trans th th′)) (lookup^R ρ^R k) ⟩
          lookup vs∘ρ k (⊆-trans th th′)
            ≡⟨⟩
          lookup vs∘ρ′₀ (σ ∷ʳ k) th′
            ∎ where

          vs′′ = Closed.next th^Env□ vs′ th′
          vs″  = Closed.next th^Env□ vs (⊆-trans th th′)

          vs-eq : All _ _≡_ (vs′′ ⊚ bind) vs″
          lookup^R vs-eq (refl ∷ k) = iext $ ext $ λ th′′ → begin
            lookup (vs′′ ⊚ bind) (refl ∷ k) th′′
              ≡⟨⟩
            lookup vs (refl ∷ ⊆-trans k ⊆-refl) (⊆-trans th (⊆-trans th′ th′′))
              ≡⟨ cong₂ (λ k → lookup vs (refl ∷ k))
                       (⊆-trans-reflʳ k)
                       (sym $ ⊆-trans-assoc th th′ th′′)
              ⟩
            lookup vs (refl ∷ k) (⊆-trans (⊆-trans th th′) th′′)
              ≡⟨⟩
            lookup vs″ (refl ∷ k) th′′
              ∎
          lookup^R vs-eq (y ∷ʳ k) = iext $ ext $ λ th′′ → begin
            lookup (vs′′ ⊚ bind) (y ∷ʳ k) th′′
              ≡⟨⟩
            lookup vs (y ∷ʳ ⊆-trans k ⊆-refl) (⊆-trans th (⊆-trans th′ th′′))
              ≡⟨ cong₂ (λ k → lookup vs (y ∷ʳ k))
                       (⊆-trans-reflʳ k)
                       (sym $ ⊆-trans-assoc th th′ th′′)
              ⟩
            lookup vs (y ∷ʳ k) (⊆-trans (⊆-trans th th′) th′′)
              ≡⟨⟩
            lookup vs″ (y ∷ʳ k) th′′ ∎
