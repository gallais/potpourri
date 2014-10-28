{-# OPTIONS --no-termination #-}

module GodelT where

open import Function
open import lib.Function

open import lib.Context
open Context
open BelongsTo

infixr 5 _`→_
data ty : Set where
  `b `ℕ : ty
  _`→_  : (σ τ : ty) → ty

module TM where

  data Tm (Γ : Con ty) : ty → Set where
    var      : {σ : ty} (v : σ ∈ Γ) → Tm Γ σ
    lam      : {σ τ : ty} (b : Tm (Γ ∙ σ) τ) → Tm Γ (σ `→ τ)
    app      : {σ τ : ty} (f : Tm Γ $ σ `→ τ) (t : Tm Γ σ) → Tm Γ τ
    zro      : Tm Γ `ℕ
    suc      : Tm Γ `ℕ → Tm Γ `ℕ
    rec[_,_] : {σ : ty} (s : Tm Γ (`ℕ `→ σ `→ σ)) (z : Tm Γ σ) → Tm Γ σ

_─_ : {σ : ty} (Γ : Con ty) (v : σ ∈ Γ) → Con ty
Γ ∙ σ ─ zro   = Γ
Γ ∙ τ ─ suc v = (Γ ─ v) ∙ τ

wkVar : {Γ : Con ty} {σ τ : ty} (v : σ ∈ Γ) (w : τ ∈ Γ ─ v) → τ ∈ Γ
wkVar zro     w       = suc w
wkVar (suc v) zro     = zro
wkVar (suc v) (suc w) = suc $ wkVar v w

data ¬Arrow : (σ : ty) → Set where
  `b : ¬Arrow `b
  `ℕ : ¬Arrow `ℕ

mutual

  data Nf (Γ : Con ty) : ty → Set where
    lam : {σ τ : ty} (b : Nf (Γ ∙ σ) τ) → Nf Γ $ σ `→ τ
    zro : Nf Γ `ℕ
    suc : Nf Γ `ℕ → Nf Γ `ℕ
    emb : {σ : ty} ⦃ ¬Ar : ¬Arrow σ ⦄ (ne : Ne Γ σ) → Nf Γ σ

  data Ne (Γ : Con ty) (υ : ty) : Set where
    elim : {τ : ty} (v : τ ∈ Γ) (sp : Sp Γ υ τ) → Ne Γ υ

  data El (Γ : Con ty) (σ : ty) : (τ : ty) → Set where
    app      : {τ : ty} → Nf Γ τ → El Γ σ (τ `→ σ)
    rec[_,_] : Nf Γ (`ℕ `→ σ `→ σ) → Nf Γ σ → El Γ σ `ℕ

  infixr 5 _<_
  data Sp (Γ : Con ty) (σ : ty) : (τ : ty) → Set where
    ε   : Sp Γ σ σ
    _<_ : {τ υ : ty} (nf : El Γ τ υ) (sp : Sp Γ σ τ) →
          Sp Γ σ υ

mutual

  wkNf : {Γ : Con ty} {σ τ : ty} (v : σ ∈ Γ) (nf : Nf (Γ ─ v) τ) → Nf Γ τ
  wkNf v (lam nf) = lam $ wkNf (suc v) nf
  wkNf v zro      = zro
  wkNf v (suc nf) = suc (wkNf v nf)
  wkNf v (emb ne) = emb $ wkNe v ne

  wkNe : {Γ : Con ty} {σ τ : ty} (v : σ ∈ Γ) (ne : Ne (Γ ─ v) τ) → Ne Γ τ
  wkNe v (elim w sp) = elim (wkVar v w) (wkSp v sp)

  wkEl : {Γ : Con ty} {σ τ₁ τ₂ : ty} (v : σ ∈ Γ) (ne : El (Γ ─ v) τ₁ τ₂) → El Γ τ₁ τ₂
  wkEl v (app u)      = app $ wkNf v u
  wkEl v rec[ s , z ] = rec[ wkNf v s , wkNf v z ]

  wkSp : {Γ : Con ty} {σ τ₁ τ₂ : ty} (v : σ ∈ Γ) (sp : Sp (Γ ─ v) τ₁ τ₂) → Sp Γ τ₁ τ₂
  wkSp v ε         = ε
  wkSp v (el < sp) = wkEl v el < wkSp v sp


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


_>_ : {Γ : Con ty} {σ τ υ : ty} (sp : Sp Γ τ σ) (el : El Γ υ τ) → Sp Γ υ σ
ε         > el = el < ε
(nf < sp) > el = nf < sp > el

_`$_ : {Γ : Con ty} {σ τ : ty} (ne : Ne Γ σ) (el : El Γ τ σ) → Ne Γ τ
elim v sp `$ el = elim v (sp > el)

eta : {Γ : Con ty} (σ : ty) (ne : Ne Γ σ) → Nf Γ σ
eta `b       ne = emb ne
eta `ℕ       ne = emb ne
eta (σ `→ τ) ne = lam $ eta τ (wkNe zro ne `$ app (eta σ $ elim zro ε))

mutual

  _[_∷=_]Nf : {Γ : Con ty} {σ τ : ty} (t : Nf Γ σ)
              (v : τ ∈ Γ) (u : Nf (Γ ─ v) τ) → Nf (Γ ─ v) σ
  lam t                      [ v  ∷= nf ]Nf = lam (t [ suc v ∷= wkNf zro nf ]Nf)
  zro                        [ v  ∷= nf ]Nf = zro
  suc t                      [ v  ∷= nf ]Nf = suc (t [ v ∷= nf ]Nf)
  emb (elim v sp)            [ w  ∷= nf ]Nf with eq? w v
  emb (elim v sp)            [ .v ∷= nf ]Nf | same .v   = elimNf nf (sp [ v ∷= nf ]Sp)
  emb (elim .(wkVar v w) sp) [ v  ∷= nf ]Nf | diff .v w = emb (elim w (sp [ v ∷= nf ]Sp))

  infixl 3 _[_∷=_]Sp
  _[_∷=_]Sp : {Γ : Con ty} {σ₁ σ₂ τ : ty} (sp : Sp Γ σ₁ σ₂)
              (v : τ ∈ Γ) (u : Nf (Γ ─ v) τ) → Sp (Γ ─ v) σ₁ σ₂
  ε       [ v ∷= nf ]Sp = ε
  hd < sp [ v ∷= nf ]Sp = hd [ v ∷= nf ]El < (sp [ v ∷= nf ]Sp)

  _[_∷=_]El : {Γ : Con ty} {σ₁ σ₂ τ : ty} (sp : El Γ σ₁ σ₂)
              (v : τ ∈ Γ) (u : Nf (Γ ─ v) τ) → El (Γ ─ v) σ₁ σ₂
  app u        [ v ∷= nf ]El = app (u [ v ∷= nf ]Nf)
  rec[ s , z ] [ v ∷= nf ]El = rec[ s [ v ∷= nf ]Nf , z [ v ∷= nf ]Nf ]

  elimNf : {Γ : Con ty} {σ υ : ty} (nf : Nf Γ σ) (Sp : Sp Γ υ σ) → Nf Γ υ
  elimNf nf       ε                   = nf
  elimNf (lam nf) (app u < sp)        = elimNf (nf [ zro ∷= u ]Nf) sp
  elimNf zro      (rec[ s , z ] < sp) = elimNf z sp
  elimNf (suc nf) (rec[ s , z ] < sp) = elimNf s (app nf < app (elimNf nf (rec[ s , z ] < ε)) < sp)
  elimNf (emb ne) (rec[ s , z ] < sp) = elimNf (eta _ (ne `$ rec[ s , z ])) sp
  elimNf (emb {{ () }} ne) (app u < sp)

open import Data.Nat as Nat using (ℕ)
open import Relation.Binary.PropositionalEquality

fromℕ : ℕ → Nf ε `ℕ
fromℕ 0           = zro
fromℕ (Nat.suc n) = suc (fromℕ n)

example :
  let plus : Nf ε (`ℕ `→ `ℕ `→ `ℕ)
      plus = lam (lam (emb (elim (suc zro) (rec[ lam (lam (suc (emb (elim zro ε)))) , emb (elim zro ε) ] < ε))))
  in elimNf plus (app (fromℕ 2) < app (fromℕ 3) < ε) ≡ fromℕ 5
example = refl