module papers.hs10.hs10 where

-- This contains the normalization procedure described in
-- Keller & Altenkirch's 2010 paper titled:
-- Hereditary Substitutions for Simple Types, Formalized

open import lib.Context
open import Function
open import lib.Function

open import lib.Context
open Context
open BelongsTo

data Ty : Set where
  `b   : Ty
  _`→_ : (σ τ : Ty) → Ty

data Tm (Γ : Con Ty) : Ty → Set where
  var : {σ : Ty} (v : σ ∈ Γ) → Tm Γ σ
  lam : {σ τ : Ty} (b : Tm (Γ ∙ σ) τ) → Tm Γ (σ `→ τ)
  app : {σ τ : Ty} (f : Tm Γ $ σ `→ τ) (t : Tm Γ σ) → Tm Γ τ

_─_ : {σ : Ty} (Γ : Con Ty) (v : σ ∈ Γ) → Con Ty
Γ ∙ σ ─ zro   = Γ
Γ ∙ τ ─ suc v = (Γ ─ v) ∙ τ

wkVar : {Γ : Con Ty} {σ τ : Ty} (v : σ ∈ Γ) (w : τ ∈ Γ ─ v) → τ ∈ Γ
wkVar zro     w       = suc w
wkVar (suc v) zro     = zro
wkVar (suc v) (suc w) = suc $ wkVar v w

wkTm : {Γ : Con Ty} {σ τ : Ty} (v : σ ∈ Γ) (tm : Tm (Γ ─ v) τ) → Tm Γ τ
wkTm v (var w)    = var $ wkVar v w
wkTm v (lam tm)   = lam $ wkTm (suc v) tm
wkTm v (app f tm) = wkTm v f ` app ` wkTm v tm

mutual

  data Nf (Γ : Con Ty) : (σ : Ty) → Set where
    lam : {σ τ : Ty} (b : Nf (Γ ∙ σ) τ) → Nf Γ $ σ `→ τ
    emb : (ne : Ne Γ `b) → Nf Γ `b

  data Ne (Γ : Con Ty) (σ : Ty) : Set where
    app : {τ : Ty} (v : τ ∈ Γ) (sp : Sp Γ σ τ) → Ne Γ σ


  infixl 5 _<_
  data Sp (Γ : Con Ty) (σ : Ty) : (τ : Ty) → Set where
    ε   : Sp Γ σ σ
    _<_ : {τ₁ τ₂ : Ty} (nf : Nf Γ τ₁) (sp : Sp Γ σ τ₂) →
          Sp Γ σ (τ₁ `→ τ₂)

mutual

  ｢_｣Nf : {Γ : Con Ty} {σ : Ty} (nf : Nf Γ σ) → Tm Γ σ
  ｢ lam nf ｣Nf = lam ｢ nf ｣Nf
  ｢ emb ne ｣Nf = ｢ ne ｣Ne

  ｢_｣Ne : {Γ : Con Ty} {σ : Ty} (ne : Ne Γ σ) → Tm Γ σ
  ｢ app v sp ｣Ne = var v $｢ sp ｣Sp

  _$｢_｣Sp : {Γ : Con Ty} {σ τ : Ty} (t : Tm Γ τ) (sp : Sp Γ σ τ) → Tm Γ σ
  t $｢ ε       ｣Sp = t
  t $｢ nf < sp ｣Sp = (t ` app ` ｢ nf ｣Nf) $｢ sp ｣Sp

mutual

  wkNf : {Γ : Con Ty} {σ τ : Ty} (v : σ ∈ Γ) (nf : Nf (Γ ─ v) τ) → Nf Γ τ
  wkNf v (lam nf) = lam (wkNf (suc v) nf)
  wkNf v (emb ne) = emb $ wkNe v ne

  wkNe : {Γ : Con Ty} {σ τ : Ty} (v : σ ∈ Γ) (ne : Ne (Γ ─ v) τ) → Ne Γ τ
  wkNe v (app w sp) = wkVar v w ` app ` wkSp v sp

  wkSp : {Γ : Con Ty} {σ τ₁ τ₂ : Ty} (v : σ ∈ Γ) (sp : Sp (Γ ─ v) τ₁ τ₂) → Sp Γ τ₁ τ₂
  wkSp v ε         = ε
  wkSp v (nf < sp) = wkNf v nf < wkSp v sp

appSp : {Γ : Con Ty} {σ₁ σ₂ τ : Ty} (sp : Sp Γ (σ₁ `→ σ₂) τ)
        (nf : Nf Γ σ₁) → Sp Γ σ₂ τ
appSp ε         nf = nf < ε
appSp (hd < sp) nf = hd < appSp sp nf

appNe : {Γ : Con Ty} {σ τ : Ty} (ne : Ne Γ $ σ `→ τ ) (nf : Nf Γ σ) → Ne Γ τ
appNe (app v sp) nf = app v (appSp sp nf)

Ne2Nf : {Γ : Con Ty} (σ : Ty) (ne : Ne Γ σ) → Nf Γ σ
Ne2Nf `b       ne = emb ne
Ne2Nf (σ `→ τ) ne = lam (Ne2Nf τ $ wkNe zro ne ` appNe ` Ne2Nf σ (app zro ε))

data Eq? {Γ : Con Ty} {σ : Ty} : (v : σ ∈ Γ) {τ : Ty} (w : τ ∈ Γ) → Set where
  same : (v : σ ∈ Γ) → Eq? v v
  diff : (v : σ ∈ Γ) {τ : Ty} (w : τ ∈ Γ ─ v) → Eq? v (wkVar v w)

eq? : {Γ : Con Ty} {σ τ : Ty} (v : σ ∈ Γ) (w : τ ∈ Γ) → Eq? v w
eq? zro     zro     = same zro
eq? zro     (suc w) = diff zro w
eq? (suc v) zro     = diff (suc v) zro
eq? (suc v) (suc w) with eq? v w
eq? (suc v) (suc .v)           | same .v   = same (suc v)
eq? (suc v) (suc .(wkVar v w)) | diff .v w = diff (suc v) (suc w)

mutual

  _[_∷=_]Nf : {Γ : Con Ty} {σ τ : Ty} (t : Nf Γ σ)
              (v : τ ∈ Γ) (u : Nf (Γ ─ v) τ) → Nf (Γ ─ v) σ
  lam t                     [ v  ∷= u ]Nf = lam (t [ suc v ∷= wkNf zro u ]Nf)
  emb (app v sp)            [ w  ∷= u ]Nf with eq? w v
  emb (app v sp)            [ .v ∷= u ]Nf | same .v   = u ` appNf ` sp [ v ∷= u ]Sp
  emb (app .(wkVar v w) sp) [ v  ∷= u ]Nf | diff .v w = emb (app w (sp [ v ∷= u ]Sp))

  infixl 3 _[_∷=_]Sp
  _[_∷=_]Sp : {Γ : Con Ty} {σ₁ σ₂ τ : Ty} (sp : Sp Γ σ₁ σ₂)
              (v : τ ∈ Γ) (u : Nf (Γ ─ v) τ) → Sp (Γ ─ v) σ₁ σ₂
  ε       [ v ∷= u ]Sp = ε
  nf < sp [ v ∷= u ]Sp = (nf [ v ∷= u ]Nf) < (sp [ v ∷= u ]Sp)

  appNf : {Γ : Con Ty} {σ τ : Ty} (nf : Nf Γ σ) (sp : Sp Γ τ σ) → Nf Γ τ
  appNf nf      ε         = nf
  appNf (lam b) (nf < sp) = b [ zro ∷= nf ]Nf ` appNf ` sp

norm : {Γ : Con Ty} {σ : Ty} (t : Tm Γ σ) → Nf Γ σ
norm (var v)   = Ne2Nf _ (app v ε)
norm (lam t)   = lam (norm t)
norm (app f t) = norm f ` appNf ` norm t < ε
