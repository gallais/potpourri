module papers.hs99.STLCSum where

-- This development is inspired by the amazing paper
-- Short Proofs of Normalization by Joachimski & Matthes (1999)
-- It implements a normalizer for STLC + sum types with *eta rules
-- for sums* and arrows based on hereditary substitution.

open import Function
open import lib.Function

open import lib.Context
open Context
open BelongsTo

data ty : Set where
  `b        : ty
  _`→_ _`+_ : (σ τ : ty) → ty

module TM where

  data Tm (Γ : Con ty) : ty → Set where
    var    : {σ : ty} (v : σ ∈ Γ) → Tm Γ σ
    lam    : {σ τ : ty} (b : Tm (Γ ∙ σ) τ) → Tm Γ (σ `→ τ)
    app    : {σ τ : ty} (f : Tm Γ $ σ `→ τ) (t : Tm Γ σ) → Tm Γ τ
    inj₁   : {σ τ : ty} (b : Tm Γ σ) → Tm Γ (σ `+ τ)
    inj₂   : {σ τ : ty} (b : Tm Γ τ) → Tm Γ (σ `+ τ)
    [_,_]  : {σ τ υ : ty} (lft : Tm (Γ ∙ σ) υ) (rgt : Tm (Γ ∙ τ) υ)
             (s : Tm Γ (σ `+ τ)) → Tm Γ υ

infixl 15 _─_

_─_ : {σ : ty} (Γ : Con ty) (v : σ ∈ Γ) → Con ty
Γ ∙ σ ─ zro   = Γ
Γ ∙ τ ─ suc v = (Γ ─ v) ∙ τ

wkVar : {Γ : Con ty} {σ τ : ty} (v : σ ∈ Γ) (w : τ ∈ Γ ─ v) → τ ∈ Γ
wkVar zro     w       = suc w
wkVar (suc v) zro     = zro
wkVar (suc v) (suc w) = suc $ wkVar v w

data ¬Arrow : (σ : ty) → Set where
  instance `b : ¬Arrow `b
  _`+_ : (σ τ : ty) → ¬Arrow $ σ `+ τ

mutual

  data Nf (Γ : Con ty) : ty → Set where
    lam  : {σ τ : ty} (b : Nf (Γ ∙ σ) τ) → Nf Γ $ σ `→ τ
    inj₁ : {σ τ : ty} (s : Nf Γ σ) → Nf Γ $ σ `+ τ
    inj₂ : {σ τ : ty} (t : Nf Γ τ) → Nf Γ $ σ `+ τ
    emb  : {σ : ty} ⦃ ¬Ar : ¬Arrow σ ⦄ (ne : Ne Γ σ) → Nf Γ σ

  data Ne (Γ : Con ty) (υ : ty) : Set where
    app : {σ τ : ty} (v : τ ∈ Γ) (sp : Sp Γ σ τ) (cs : Cs Γ υ σ) → Ne Γ υ

  infixl 5 _<_
  data Sp (Γ : Con ty) (σ : ty) : (τ : ty) → Set where
    ε   : Sp Γ σ σ
    _<_ : {τ₁ τ₂ : ty} (nf : Nf Γ τ₁) (sp : Sp Γ σ τ₂) →
          Sp Γ σ (τ₁ `→ τ₂)

  data Cs (Γ : Con ty) (σ : ty) : (τ : ty) → Set where
    ε     : Cs Γ σ σ
    [_,_] : {τ₁ τ₂ : ty} (lft : Nf (Γ ∙ τ₁) σ) (rgt : Nf (Γ ∙ τ₂) σ) →
            Cs Γ σ (τ₁ `+ τ₂)

mutual

  wkNf : {Γ : Con ty} {σ τ : ty} (v : σ ∈ Γ) (nf : Nf (Γ ─ v) τ) → Nf Γ τ
  wkNf v (lam nf)     = lam  $ wkNf (suc v) nf
  wkNf v (inj₁ nf)    = inj₁ $ wkNf v nf
  wkNf v (inj₂ nf)    = inj₂ $ wkNf v nf
  wkNf v (emb ne) = emb $ wkNe v ne

  wkNe : {Γ : Con ty} {σ τ : ty} (v : σ ∈ Γ) (ne : Ne (Γ ─ v) τ) → Ne Γ τ
  wkNe v (app w sp cs) = app (wkVar v w) (wkSp v sp) (wkCs v cs)

  wkSp : {Γ : Con ty} {σ τ₁ τ₂ : ty} (v : σ ∈ Γ) (sp : Sp (Γ ─ v) τ₁ τ₂) → Sp Γ τ₁ τ₂
  wkSp v ε         = ε
  wkSp v (nf < sp) = wkNf v nf < wkSp v sp

  wkCs : {Γ : Con ty} {σ τ₁ τ₂ : ty} (v : σ ∈ Γ) (sp : Cs (Γ ─ v) τ₁ τ₂) → Cs Γ τ₁ τ₂
  wkCs v ε             = ε
  wkCs v [ lft , rgt ] = [ wkNf (suc v) lft , wkNf (suc v) rgt ]

 

data Eq? {Γ : Con ty} {σ : ty} : (v : σ ∈ Γ) {τ : ty} (w : τ ∈ Γ) → Set where
  same : (v : σ ∈ Γ) → Eq? v v
  diff : (v : σ ∈ Γ) {τ : ty} (w : τ ∈ Γ ─ v) → Eq? v (wkVar v w)

eq? : {Γ : Con ty} {σ τ : ty} (v : σ ∈ Γ) (w : τ ∈ Γ) → Eq? v w
eq? zro     zro     = same zro
eq? zro     (suc w) = diff zro w
eq? (suc v) zro     = diff (suc v) zro
eq? (suc v) (suc w) with eq? v w
eq? (suc v) (suc .v)           | same .v   = same (suc v)
eq? (suc v) (suc .(wkVar v w)) | diff .v w = diff (suc v) (suc w)

mutual

  _[_∷=_]Nf : {Γ : Con ty} {σ τ : ty} (t : Nf Γ σ)
              (v : τ ∈ Γ) (u : Nf (Γ ─ v) τ) → Nf (Γ ─ v) σ
  lam t                        [ v  ∷= nf ]Nf = lam $ t [ suc v ∷= wkNf zro nf ]Nf
  inj₁ t                       [ v  ∷= nf ]Nf = inj₁ $ t [ v ∷= nf ]Nf
  inj₂ t                       [ v  ∷= nf ]Nf = inj₂ $ t [ v ∷= nf ]Nf
  emb (app v sp cs)            [ w  ∷= nf ]Nf  with eq? w v
  emb (app v sp cs)            [ .v ∷= nf ]Nf | same .v   = appNf nf sp′ cs′
    where sp′ = sp [ v ∷= nf ]Sp
          cs′ = cs [ v ∷= nf ]Cs
  emb (app .(wkVar v w) sp cs) [ v  ∷= nf ]Nf | diff .v w = emb $ app w sp′ cs′
    where sp′ = sp [ v ∷= nf ]Sp
          cs′ = cs [ v ∷= nf ]Cs

  infixl 3 _[_∷=_]Sp
  _[_∷=_]Sp : {Γ : Con ty} {σ₁ σ₂ τ : ty} (sp : Sp Γ σ₁ σ₂)
              (v : τ ∈ Γ) (u : Nf (Γ ─ v) τ) → Sp (Γ ─ v) σ₁ σ₂
  ε       [ v ∷= nf ]Sp = ε
  hd < sp [ v ∷= nf ]Sp = hd [ v ∷= nf ]Nf < (sp [ v ∷= nf ]Sp)

  _[_∷=_]Cs : {Γ : Con ty} {σ₁ σ₂ τ : ty} (cs : Cs Γ σ₁ σ₂)
              (v : τ ∈ Γ) (u : Nf (Γ ─ v) τ) → Cs (Γ ─ v) σ₁ σ₂
  ε             [ v ∷= nf ]Cs = ε
  [ lft , rgt ] [ v ∷= nf ]Cs = [ lft [ suc v ∷= wkNf zro nf ]Nf
                                , rgt [ suc v ∷= wkNf zro nf ]Nf ]

  appNf : {Γ : Con ty} {σ τ υ : ty} ⦃ ¬Ar : ¬Arrow υ ⦄
          (nf : Nf Γ σ) (sp : Sp Γ τ σ) (cs : Cs Γ υ τ) → Nf Γ υ
  appNf nf                 ε         ε             = nf
  appNf (inj₁ nf)          ε         [ lft , rgt ] = lft [ zro ∷= nf ]Nf
  appNf (inj₂ nf)          ε         [ lft , rgt ] = rgt [ zro ∷= nf ]Nf
  appNf (lam b)            (nf < sp) cs            = appNf (b [ zro ∷= nf ]Nf) sp cs
  appNf (emb (app v sp ε))           ε     cs₂ = emb $ app v sp cs₂
  appNf (emb (app v sp [ l₁ , r₁ ])) ε     cs₂ = emb $ app v sp [ lft , rgt ]
    where lft = appNf l₁ ε $ wkCs zro cs₂
          rgt = appNf r₁ ε $ wkCs zro cs₂
  appNf (emb {{ () }} ne)  (nf < sp) cs

varNe : {Γ : Con ty} {σ : ty} (v : σ ∈ Γ) → Ne Γ σ
varNe v = app v ε ε

appNf′ : {Γ : Con ty} {σ τ : ty} (f : Nf Γ $ σ `→ τ) (t : Nf Γ σ) → Nf Γ τ
appNf′ (lam b) t = b [ zro ∷= t ]Nf
appNf′ (emb ⦃ () ⦄ _) _


appSp : {Γ : Con ty} {σ₁ σ₂ τ : ty} (sp : Sp Γ (σ₁ `→ σ₂) τ)
        (nf : Nf Γ σ₁) → Sp Γ σ₂ τ
appSp ε         nf = nf < ε
appSp (hd < sp) nf = hd < appSp sp nf

appNe : {Γ : Con ty} {σ τ : ty} (ne : Ne Γ $ σ `→ τ ) (nf : Nf Γ σ) → Ne Γ τ
appNe (app v sp ε)             nf = app v (appSp sp nf) ε
appNe (app v sp [ lft , rgt ]) nf = app v sp [ lft′ , rgt′ ]
  where lft′ = lft ` appNf′ ` wkNf zro nf
        rgt′ = rgt ` appNf′ ` wkNf zro nf

Ne2Nf : {Γ : Con ty} (σ : ty) (ne : Ne Γ σ) → Nf Γ σ
Ne2Nf `b       ne = emb ne
Ne2Nf (σ `→ τ) ne = lam $ Ne2Nf τ $ wkNe zro ne ` appNe ` Ne2Nf σ (varNe zro)
Ne2Nf (σ `+ τ) ne = emb ⦃ _ `+ _ ⦄ ne

mutual

  elimSumNe : ∀ {Γ σ₁ σ₂ τ} (t₁ : Nf (Γ ∙ σ₁) τ) (t₂ : Nf (Γ ∙ σ₂) τ)
              (s : Ne Γ (σ₁ `+ σ₂)) → Ne Γ τ
  elimSumNe t₁ t₂ (app v sp ε)             = app v sp [ t₁ , t₂ ]
  elimSumNe t₁ t₂ (app v sp [ lft , rgt ]) = app v sp [ lft′ , rgt′ ]
    where lft′ = elimSum (wkNf (suc zro) t₁) (wkNf (suc zro) t₂) lft
          rgt′ = elimSum (wkNf (suc zro) t₁) (wkNf (suc zro) t₂) rgt

  elimSum : ∀ {Γ σ₁ σ₂ τ} (t₁ : Nf (Γ ∙ σ₁) τ) (t₂ : Nf (Γ ∙ σ₂) τ)
            (s : Nf Γ (σ₁ `+ σ₂)) → Nf Γ τ
  elimSum t₁ t₂ (inj₁ s) = t₁ [ zro ∷= s ]Nf
  elimSum t₁ t₂ (inj₂ s) = t₂ [ zro ∷= s ]Nf
  elimSum t₁ t₂ (emb ne) = Ne2Nf _ $ elimSumNe t₁ t₂ ne

open TM

norm : {Γ : Con ty} {σ : ty} (t : TM.Tm Γ σ) → Nf Γ σ
norm (var v)         = Ne2Nf _ (varNe v)
norm (lam t)         = lam (norm t)
norm (app f t)       = norm f ` appNf′ ` norm t
norm (inj₁ t)        = inj₁ (norm t)
norm (inj₂ t)        = inj₂ (norm t)
norm ([ t₁ , t₂ ] s) = elimSum (norm t₁) (norm t₂) (norm s)
