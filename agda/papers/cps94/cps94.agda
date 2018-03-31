-----------------------------------------------------------------
-- This is a formalization based on Hatcliff and Danvy's paper
-- A Generic Account of Continuation-Passing Styles (POPL 1994)
-- which factors out the CPS transformation as a translation
-- from Moggi's computational calculus back to stlc precomposed
-- with whichever embedding from stlc (depending whether one
-- wants a call-by-value or call-by-name CPS transform).

module papers.cps94.cps94 where

open import Data.List
open import Function
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

Con = List
pattern ε   = []
pattern _∙_ as a = a ∷ as

infix 5 _∈_
data _∈_ {A : Set} (a : A) : Con A → Set where
  z : ∀ {as} → a ∈ as ∙ a
  s : ∀ {b as} → a ∈ as → a ∈ as ∙ b 

infix 5 _⊆_
_⊆_ : {A : Set} → Con A → Con A → Set
Γ ⊆ Δ = ∀ {a} → a ∈ Γ → a ∈ Δ

refl = id

step : {A : Set} {a : A} {Γ Δ : Con A} → Γ ⊆ Δ → Γ ⊆ Δ ∙ a
step inc = s ∘ inc

pop! : {A : Set} {a : A} {Γ Δ : Con A} → Γ ⊆ Δ → Γ ∙ a ⊆ Δ ∙ a
pop! inc z     = z
pop! inc (s v) = s (inc v)

map∈ : {A B : Set} {Γ : Con A} {σ : A} (f : A → B) → σ ∈ Γ → f σ ∈ map f Γ
map∈ f z     = z
map∈ f (s x) = s (map∈ f x)

-----------------------------------------------------------------
-- Simply-Typed Lambda-Calculus (onwards: STLC)
-- Well-typed & scoped by construction. Using de Bruijn indices
-- Enjoys weakening by Order Preserving Embeddings (Chapman's Phd).


infixr 20 _`→_

data ty : Set where
  ι    : ty
  _`→_ : (σ τ : ty) → ty

infix  5 _⊢_
infixl 20 _`$_

data _⊢_ (Γ : Con ty) : ty → Set where
  `v    : ∀ {σ}   (pr : σ ∈ Γ)                  → Γ ⊢ σ
  `λ    : ∀ {σ τ} (t  : Γ ∙ σ ⊢ τ)              → Γ ⊢ σ `→ τ
  _`$_  : ∀ {σ τ} (t  : Γ ⊢ σ `→ τ) (u : Γ ⊢ σ) → Γ ⊢ τ

wk : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) (t : Γ ⊢ σ) → Δ ⊢ σ
wk inc (`v pr)  = `v (inc pr)
wk inc (`λ t)   = `λ (wk (pop! inc) t)
wk inc (f `$ t) = wk inc f `$ wk inc t


-----------------------------------------------------------------
-- Calculus based on Moggi's computational meta-language (onwards: ML)
-- Compared to STLC, it adds a computation type and "monadic"
-- operations (that is, their semantics should be a monad)
-- Well-typed & scoped by construction. Using de Bruijn indices


infix 30 &_

data ty-ml : Set where
  ι    : ty-ml
  _`→_ : (σ τ : ty-ml) → ty-ml
  &_   : (σ : ty-ml)   → ty-ml

infix  5 _⊢ml_
infixr 10 _⟫=_

data _⊢ml_ (Γ : Con ty-ml) : ty-ml → Set where
  `v    : ∀ {σ}   (pr : σ ∈ Γ)                          → Γ ⊢ml σ
  `λ    : ∀ {σ τ} (t  : Γ ∙ σ ⊢ml & τ)                  → Γ ⊢ml σ `→ & τ
  _`$_  : ∀ {σ τ} (t  : Γ ⊢ml σ `→ & τ) (u : Γ ⊢ml σ)   → Γ ⊢ml & τ
  _⟫=_  : ∀ {σ τ} (t₁ : Γ ⊢ml & σ) (t₂ : Γ ∙ σ ⊢ml & τ) → Γ ⊢ml & τ
  ret_  : ∀ {σ}   (t  : Γ ⊢ml σ)                        → Γ ⊢ml & σ

wkml : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) (t : Γ ⊢ml σ) → Δ ⊢ml σ
wkml inc (`v pr)    = `v (inc pr)
wkml inc (`λ t)     = `λ (wkml (pop! inc) t)
wkml inc (f `$ t)   = wkml inc f `$ wkml inc t
wkml inc (t₁ ⟫= t₂) = wkml inc t₁ ⟫= wkml (pop! inc) t₂
wkml inc (ret t)    = ret wkml inc t


-----------------------------------------------------------------
-- Generic CPS transform
-- Transforms terms from the computational calculus back to the
-- simply-typed one whilst preserving the sequentiality introduced
-- by _⟫=_. It is indexed by the return type (typically the type
-- of the whole computation so that we can run it by feeding the
-- identity as the base continuation).


CPS[_] : (r : ty) (σ : ty-ml) → ty
CPS[ r ] (ι     ) = ι
CPS[ r ] (σ `→ τ) = CPS[ r ] σ `→ CPS[ r ] τ
CPS[ r ] (& σ   ) = (CPS[ r ] σ `→ r) `→ r

cps[_] : ∀ {Γ σ} (r : ty) (t : Γ ⊢ml σ) → map CPS[ r ] Γ ⊢ CPS[ r ] σ
cps[ r ] (`v pr)    = `v (map∈ (CPS[ r ]) pr)
cps[ r ] (`λ t)     = `λ (cps[ r ] t)
cps[ r ] (f `$ u)   = cps[ r ] f `$ cps[ r ] u
cps[ r ] (t₁ ⟫= t₂) =
  let inc₁ = step refl
      inc₂ = pop! inc₁
      u₁   = wk inc₁ $ cps[ r ] t₁
      u₂   = wk inc₂ $ cps[ r ] t₂
  in `λ (u₁ `$ (`λ (u₂ `$ `v (s z))))
cps[ r ] (ret t)    =
  let inc = step refl
      u   = wk inc $ cps[ r ] t
  in `λ (`v z `$ u)


-----------------------------------------------------------------
-- CBV Embedding of STLC into ML
-- VValues are given a value type whilst ¬VValues get a computational
-- one. Notice how the domain of function types is a value.


mutual

  CBV : (σ : ty) → ty-ml
  CBV ι        = ι
  CBV (σ `→ τ) = CBV σ `→ &CBV τ

  &CBV : (σ : ty) → ty-ml
  &CBV σ = & CBV σ

data VValue {Γ : Con ty} : {σ : ty} (t : Γ ⊢ σ) → Set where
  `λ : ∀ {σ τ} (t : Γ ∙ σ ⊢ τ) → VValue (`λ t)
  `v : ∀ {σ}   (pr : σ ∈ Γ)    → VValue (`v pr)

data ¬VValue {Γ : Con ty} : {σ : ty} (t : Γ ⊢ σ) → Set where
  _`$_ : ∀ {σ τ} (t : Γ ⊢ σ `→ τ) (u : Γ ⊢ σ) → ¬VValue (t `$ u)

isVValue? : ∀ {Γ σ} (t : Γ ⊢ σ) → VValue t ⊎ ¬VValue t
isVValue? (`v pr)  = inj₁ (`v pr)
isVValue? (`λ t)   = inj₁ (`λ t)
isVValue? (f `$ u) = inj₂ (f `$ u)

mutual

  &cbv : ∀ {Γ σ} (t : Γ ⊢ σ) → map CBV Γ ⊢ml &CBV σ
  &cbv t with isVValue? t
  ...     | inj₁ yep!     = ret cbv yep!
  &cbv ._ | inj₂ (f `$ t) =
    let inc = step refl
        g   = &cbv f
        u   = wkml inc $ &cbv t
    in g ⟫= u ⟫= `v (s z) `$ `v z

  cbv : ∀ {Γ σ} {t : Γ ⊢ σ} (T : VValue t) → map CBV Γ ⊢ml CBV σ
  cbv (`λ t)  = `λ (&cbv t)
  cbv (`v pr) = `v (map∈ CBV pr)


-----------------------------------------------------------------
-- CBN Embedding of STLC into ML
-- Notice how the domain of function types is computational.


data NValue {Γ : Con ty} : {σ : ty} (t : Γ ⊢ σ) → Set where
  `λ : ∀ {σ τ} (t : Γ ∙ σ ⊢ τ) → NValue (`λ t)

data ¬NValue {Γ : Con ty} : {σ : ty} (t : Γ ⊢ σ) → Set where
  _`$_ : ∀ {σ τ} (t : Γ ⊢ σ `→ τ) (u : Γ ⊢ σ) → ¬NValue (t `$ u)
  `v   : ∀ {σ}   (pr : σ ∈ Γ)                 → ¬NValue (`v pr)

isNValue? : ∀ {Γ σ} (t : Γ ⊢ σ) → NValue t ⊎ ¬NValue t
isNValue? (`v pr)  = inj₂ (`v pr)
isNValue? (`λ t)   = inj₁ (`λ t)
isNValue? (f `$ u) = inj₂ (f `$ u)

mutual

  CBN : (σ : ty) → ty-ml
  CBN ι        = ι
  CBN (σ `→ τ) = &CBN σ `→ &CBN τ

  &CBN : (σ : ty) → ty-ml
  &CBN σ = & CBN σ

mutual

  &cbn : ∀ {Γ σ} (t : Γ ⊢ σ) → map &CBN Γ ⊢ml &CBN σ
  &cbn t with isNValue? t
  ...     | inj₁ yep!     = ret cbn yep!
  &cbn ._ | inj₂ (`v pr)  = `v (map∈ &CBN pr)
  &cbn ._ | inj₂ (f `$ t) =
    let inc = step refl
        g   = &cbn f
        u   = wkml inc $ &cbn t
    in g ⟫= `v z `$ u

  cbn : ∀ {Γ σ} {t : Γ ⊢ σ} (T : NValue t) → map &CBN Γ ⊢ml CBN σ
  cbn (`λ t)  = `λ (&cbn t)


-----------------------------------------------------------------
-- CBN Embedding of STLC into ML
-- Notice how the domain of function types is computational.


cps[_]cbv : ∀ τ {Γ σ} (t : Γ ⊢ σ) → _
cps[ τ ]cbv = cps[ τ ] ∘ &cbv

cps[_]cbn : ∀ τ {Γ σ} (t : Γ ⊢ σ) → _
cps[ τ ]cbn = cps[ τ ] ∘ &cbn

`id : ∀ {Γ} (σ : ty) → Γ ⊢ σ `→ σ
`id σ = `λ (`v z)

term : ε ⊢ ι `→ ι
term = `λ ((`id (ι `→ ι) `$ `id ι) `$ `v z)

test-cbv : (σ : ty) → ε ⊢ ((ι `→ (ι `→ σ) `→ σ) `→ σ) `→ σ
test-cbv σ = cps[ σ ]cbv (`λ ((`id (ι `→ ι) `$ `id ι) `$ `v z))
