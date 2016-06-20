module papers.hs10.hs10-with-pairs where

-- This contains an extended version of the normalization procedure
-- described in Keller & Altenkirch's 2010 paper titled:
-- Hereditary Substitutions for Simple Types, Formalized

open import lib.Context
open import Function
open import lib.Function

open import lib.Context
open Context
open BelongsTo

data Ty : Set where
  `b   : Ty
  _`→_ _`×_ : (σ τ : Ty) → Ty

data Tm (Γ : Con Ty) : Ty → Set where
  var : {σ : Ty} (v : σ ∈ Γ) → Tm Γ σ
  lam : {σ τ : Ty} (b : Tm (Γ ∙ σ) τ) → Tm Γ (σ `→ τ)
  prd : {σ τ : Ty} (a : Tm Γ σ) (b : Tm Γ τ) → Tm Γ (σ `× τ)
  app : {σ τ : Ty} (f : Tm Γ (σ `→ τ)) (t : Tm Γ σ) → Tm Γ τ
  fst : {σ τ : Ty} (p : Tm Γ (σ `× τ)) → Tm Γ σ
  snd : {σ τ : Ty} (p : Tm Γ (σ `× τ)) → Tm Γ τ
  
infix 10 _─_
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
wkTm v (prd a b)  = prd (wkTm v a) (wkTm v b)
wkTm v (app f tm) = wkTm v f ` app ` wkTm v tm
wkTm v (fst p)    = fst $ wkTm v p
wkTm v (snd p)    = snd $ wkTm v p

mutual

  data Nf (Γ : Con Ty) : (σ : Ty) → Set where
    lam : {σ τ : Ty} (b : Nf (Γ ∙ σ) τ) → Nf Γ $ σ `→ τ
    prd : {σ τ : Ty} (a : Nf Γ σ) (b : Nf Γ τ) → Nf Γ $ σ `× τ
    emb : (ne : Ne Γ `b) → Nf Γ `b

  data Ne (Γ : Con Ty) (σ : Ty) : Set where
    app :  {τ : Ty} (v : τ ∈ Γ) (sp : Sp Γ σ τ) → Ne Γ σ

  infixl 5 _<_
  data Sp (Γ : Con Ty) (σ : Ty) : (τ : Ty) → Set where
    ε     : Sp Γ σ σ
    _<_   : {τ₁ τ₂ : Ty} (nf : Nf Γ τ₁) (sp : Sp Γ σ τ₂) → Sp Γ σ (τ₁ `→ τ₂)
    fst<_ : {τ₁ τ₂ : Ty} (sp : Sp Γ σ τ₁) → Sp Γ σ (τ₁ `× τ₂)
    snd<_ : {τ₁ τ₂ : Ty} (sp : Sp Γ σ τ₂) → Sp Γ σ (τ₁ `× τ₂)
    
mutual

  ｢_｣Nf : {Γ : Con Ty} {σ : Ty} (nf : Nf Γ σ) → Tm Γ σ
  ｢ lam nf  ｣Nf = lam ｢ nf ｣Nf
  ｢ prd a b ｣Nf = prd ｢ a ｣Nf ｢ b ｣Nf
  ｢ emb ne  ｣Nf = ｢ ne ｣Ne

  ｢_｣Ne : {Γ : Con Ty} {σ : Ty} (ne : Ne Γ σ) → Tm Γ σ
  ｢ app v sp ｣Ne = var v $｢ sp ｣Sp

  _$｢_｣Sp : {Γ : Con Ty} {σ τ : Ty} (t : Tm Γ τ) (sp : Sp Γ σ τ) → Tm Γ σ
  t $｢ ε       ｣Sp = t
  t $｢ nf < sp ｣Sp = (t ` app ` ｢ nf ｣Nf) $｢ sp ｣Sp
  t $｢ fst< sp ｣Sp = fst t $｢ sp ｣Sp
  t $｢ snd< sp ｣Sp = snd t $｢ sp ｣Sp

mutual

  wkNf : {Γ : Con Ty} {σ τ : Ty} (v : σ ∈ Γ) (nf : Nf (Γ ─ v) τ) → Nf Γ τ
  wkNf v (lam nf)  = lam (wkNf (suc v) nf)
  wkNf v (prd a b) = prd (wkNf v a) (wkNf v b)
  wkNf v (emb ne)  = emb $ wkNe v ne

  wkNe : {Γ : Con Ty} {σ τ : Ty} (v : σ ∈ Γ) (ne : Ne (Γ ─ v) τ) → Ne Γ τ
  wkNe v (app w sp) = wkVar v w ` app ` wkSp v sp

  wkSp : {Γ : Con Ty} {σ τ₁ τ₂ : Ty} (v : σ ∈ Γ) (sp : Sp (Γ ─ v) τ₁ τ₂) → Sp Γ τ₁ τ₂
  wkSp v ε         = ε
  wkSp v (nf < sp) = wkNf v nf < wkSp v sp
  wkSp v (fst< sp) = fst< wkSp v sp
  wkSp v (snd< sp) = snd< wkSp v sp

appSp : {Γ : Con Ty} {σ₁ σ₂ τ : Ty} (sp : Sp Γ (σ₁ `→ σ₂) τ)
        (nf : Nf Γ σ₁) → Sp Γ σ₂ τ
appSp ε         nf = nf < ε
appSp (hd < sp) nf = hd < appSp sp nf
appSp (fst< sp) nf = fst< appSp sp nf
appSp (snd< sp) nf = snd< appSp sp nf

fstSp : {Γ : Con Ty} {σ₁ σ₂ τ : Ty} (sp : Sp Γ (σ₁ `× σ₂) τ) → Sp Γ σ₁ τ
fstSp ε         = fst< ε
fstSp (nf < sp) = nf < fstSp sp
fstSp (fst< sp) = fst< fstSp sp
fstSp (snd< sp) = snd< fstSp sp

sndSp : {Γ : Con Ty} {σ₁ σ₂ τ : Ty} (sp : Sp Γ (σ₁ `× σ₂) τ) → Sp Γ σ₂ τ
sndSp ε         = snd< ε
sndSp (nf < sp) = nf < sndSp sp
sndSp (fst< sp) = fst< sndSp sp
sndSp (snd< sp) = snd< sndSp sp

appNe : {Γ : Con Ty} {σ τ : Ty} (ne : Ne Γ $ σ `→ τ ) (nf : Nf Γ σ) → Ne Γ τ
appNe (app v sp) nf = app v (appSp sp nf)

fstNe : {Γ : Con Ty} {σ τ : Ty} (ne : Ne Γ $ σ `× τ ) → Ne Γ σ
fstNe (app v sp) = app v (fstSp sp)

sndNe : {Γ : Con Ty} {σ τ : Ty} (ne : Ne Γ $ σ `× τ ) → Ne Γ τ
sndNe (app v sp) = app v (sndSp sp)

Ne2Nf : {Γ : Con Ty} (σ : Ty) (ne : Ne Γ σ) → Nf Γ σ
Ne2Nf `b       ne = emb ne
Ne2Nf (σ `→ τ) ne = lam (Ne2Nf τ $ wkNe zro ne ` appNe ` Ne2Nf σ (app zro ε))
Ne2Nf (σ `× τ) ne = prd (Ne2Nf σ (fstNe ne)) (Ne2Nf τ (sndNe ne))

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
  prd a b                   [ v  ∷= u ]Nf = prd (a [ v ∷= u ]Nf) (b [ v ∷= u ]Nf)
  emb (app v sp)            [ w  ∷= u ]Nf with eq? w v
  emb (app v sp)            [ .v ∷= u ]Nf | same .v   = u ` appNf ` sp [ v ∷= u ]Sp
  emb (app .(wkVar v w) sp) [ v  ∷= u ]Nf | diff .v w = emb (app w (sp [ v ∷= u ]Sp))

  infixl 3 _[_∷=_]Sp
  _[_∷=_]Sp : {Γ : Con Ty} {σ₁ σ₂ τ : Ty} (sp : Sp Γ σ₁ σ₂)
              (v : τ ∈ Γ) (u : Nf (Γ ─ v) τ) → Sp (Γ ─ v) σ₁ σ₂
  ε       [ v ∷= u ]Sp = ε
  nf < sp [ v ∷= u ]Sp = (nf [ v ∷= u ]Nf) < (sp [ v ∷= u ]Sp)
  fst< sp [ v ∷= u ]Sp = fst< (sp [ v ∷= u ]Sp) 
  snd< sp [ v ∷= u ]Sp = snd< (sp [ v ∷= u ]Sp) 
    
  appNf : {Γ : Con Ty} {σ τ : Ty} (nf : Nf Γ σ) (sp : Sp Γ τ σ) → Nf Γ τ
  appNf nf        ε         = nf
  appNf (lam b)   (nf < sp) = b [ zro ∷= nf ]Nf ` appNf ` sp
  appNf (prd a b) (fst< sp) = appNf a sp
  appNf (prd a b) (snd< sp) = appNf b sp
  
norm : {Γ : Con Ty} {σ : Ty} (t : Tm Γ σ) → Nf Γ σ
norm (var v)   = Ne2Nf _ (app v ε)
norm (lam t)   = lam (norm t)
norm (prd a b) = prd (norm a) (norm b)
norm (app f t) = norm f ` appNf ` norm t < ε
norm (fst p)   = norm p ` appNf ` fst< ε
norm (snd p)   = norm p ` appNf ` snd< ε

