{-# OPTIONS --type-in-type               #-}
{-# OPTIONS --injective-type-constructor #-}

module unif where

open import Data.Fin
open import Data.Nat
open import Data.Maybe
open import Function hiding (_∋_)
open import Category.Monad

module MM = RawMonad   (monad   {_})
open MM

open import Relation.Nullary
open import lib.Nullary
open import Relation.Binary.PropositionalEquality

postulate
  eq : {A : Set} (a b : A) → Dec (a ≡ b)

infix 1 _⊆_ _⊆′_ _∋_
data _⊆_ : (A B : Set) → Set where
  refl : ∀ {A} → A ⊆ A
  pop! : ∀ {A B} → A ⊆ B → Maybe A ⊆ Maybe B
  step : ∀ {A B} → A ⊆ B → A ⊆ Maybe B

data _⊆′_ : (A B : Set) → Set where
  refl : ∀ {A} → A ⊆′ A
  step : ∀ {A B} → A ⊆′ B → A ⊆′ Maybe B

wk : ∀ {A B} (le : A ⊆ B) (a : A) → B
wk refl      a = a
wk (pop! le) a = map (wk le) a
wk (step le) a = just $ wk le a

wk′ : ∀ {A B} (le : A ⊆′ B) (a : A) → B
wk′ refl      a = a
wk′ (step le) a = just $ wk′ le a

data _∋_ : (A : Set) (a : A) → Set where
  z : ∀ {A} → Maybe A ∋ nothing
  s : ∀ {A a} → A ∋ a → Maybe A ∋ just a

infix 5 _─_
_─_ : ∀ A {a} → A ∋ a → Set
._ ─ z {A}   = A
._ ─ s {A} v = Maybe $ A ─ v

mutual

  data Nf (A : Set) : Set where
    lam : Nf (Maybe A) → Nf A
    zro : Nf A
    suc : Nf A → Nf A
    neu : (ne : Ne A) → Nf A

  data Ne (A : Set) : Set where
    var : (a : A) → Ne A
    app : Ne A → (nf : Nf A) → Ne A

mutual

  mapNf : {A B : Set} (f : A → B) → Nf A → Nf B
  mapNf f (lam nf) = lam $ mapNf (maybe (just ∘ f) nothing) nf
  mapNf f zro      = zro
  mapNf f (suc nf) = suc $ mapNf f nf
  mapNf f (neu ne) = neu $ mapNe f ne

  mapNe : {A B : Set} (f : A → B) → Ne A → Ne B
  mapNe f (var a)     = var $ f a
  mapNe f (app ne nf) = app (mapNe f ne) (mapNf f nf)

wkNf : {A : Set} → Nf A → Nf (Maybe A)
wkNf = mapNf just

wkNe : {A : Set} → Ne A → Ne (Maybe A)
wkNe = mapNe just

thining : ∀ {A a} (v : A ∋ a) → A → Maybe (A ─ v)
thining z     w = w
thining (s v) w = maybe (map just ∘ thining v) nothing w

wk∋ : ∀ {A B a} (le : A ⊆ B) (v : A ∋ a) → B ∋ wk le a
wk∋ refl      v     = v
wk∋ (pop! le) z     = z
wk∋ (pop! le) (s v) = s $ wk∋ le v
wk∋ (step le) v     = s $ wk∋ le v

mutual

  thiningNf : ∀ {A a} (v : A ∋ a) → Nf A → Maybe (Nf $ A ─ v)
  thiningNf v (lam nf) = map lam $ thiningNf (s v) nf
  thiningNf v zro      = just zro
  thiningNf v (suc nf) = map suc $ thiningNf v nf
  thiningNf v (neu ne) = map neu $ thiningNe v ne

  thiningNe : ∀ {A a} (v : A ∋ a) → Ne A → Maybe (Ne $ A ─ v)
  thiningNe v (var w)     = map var $ thining v w
  thiningNe v (app ne nf) =
    maybe (λ ne′ → map (app ne′) $ thiningNf v nf) nothing (thiningNe v ne)

thiningsNf : {A B : Set} (inc : A ⊆′ B) → Nf B → Maybe (Nf A)
thiningsNf refl       nf = just nf
thiningsNf (step inc) nf = thiningNf z nf >>= thiningsNf inc

data Subst : (A B : Set) → ℕ → Set where
  base : ∀ {A} → Subst A A 0
  meta : ∀ {A B} → Subst A B 0 → Subst A (Maybe B) 0
  bind : ∀ {A B} → Nf A → Subst A B 0 → Subst A (Maybe B) 0
  same : ∀ {A B n} → Subst A B n → Subst (Maybe A) (Maybe B) (suc n)

unSame : ∀ {A B n} → Subst (Maybe A) (Maybe B) (suc n) → Subst A B n
unSame (same sub) = sub

var0 : ∀ {A} → Nf (Maybe A)
var0 = neu $ var nothing

pattern nvar b = neu (var b)

abst : {A B : Set} → A ⊆′ B → Nf B → Nf A
abst refl       nf = nf
abst (step inc) nf = abst inc (lam nf)

abstIn : {B : Set} → Nf B → B → Nf (Maybe B)
abstIn nf v = mapNf (λ w → dec (eq v w) (const nothing) (const $ just w)) nf

infix 3 _isIn?_
_isIn?_ : {A B : Set} {n : ℕ} (b : B) (sub : Subst A B n) → Maybe A
b  isIn? base       = just b
mb isIn? meta sub   = mb >>= λ b → b isIn? sub
mb isIn? bind x sub = mb >>= λ b → b isIn? sub
mb isIn? same sub   = maybe (λ b → just <$> (b isIn? sub)) (just nothing) mb

mutual

  unifyNfAgainstNf : {A B : Set} {n : ℕ} (sub : Subst A B n) → Nf A → Nf B → Maybe (Subst A B n)
  -- go through constructors
  unifyNfAgainstNf sub (lam nf) (lam nf') = unSame <$> unifyNfAgainstNf (same sub) nf nf'
  unifyNfAgainstNf sub zro      zro       = return sub
  unifyNfAgainstNf sub (suc nf) (suc nf') = unifyNfAgainstNf sub nf nf'
  -- unify neutrals
  unifyNfAgainstNf sub nf       (neu ne)  = unifyNfAgainstNe sub nf ne refl
  -- spelling out all the ways in which it can fail
  unifyNfAgainstNf _   (lam _)  zro       = nothing
  unifyNfAgainstNf _   zro      (lam _)   = nothing
  unifyNfAgainstNf _   (lam _)  (suc _)   = nothing
  unifyNfAgainstNf _   (suc _)  (lam _)   = nothing
  unifyNfAgainstNf _   (suc _)  zro       = nothing
  unifyNfAgainstNf _   zro      (suc _)   = nothing
  unifyNfAgainstNf _   (neu _)  (lam _)   = nothing
  unifyNfAgainstNf _   (neu _)  zro       = nothing
  unifyNfAgainstNf _   (neu _)  (suc _)   = nothing

  unifyNfAgainstNe : {A B C : Set} {n : ℕ} (sub : Subst A B n) → Nf C → Ne B → (A ⊆′ C) → Maybe (Subst A B n)
  -- binding
  unifyNfAgainstNe sub nf (var v)           inc = unifyVar sub (abst inc nf) v
  -- abstracting
  unifyNfAgainstNe sub nf (app ne (nvar b)) inc =
    maybe (λ a → unifyNfAgainstNe sub (abstIn nf (wk′ inc a)) ne (step inc))
    (case nf of λ
      { (neu (app ne′ nf′)) → thiningsNf inc nf   >>= λ nf′′ →
                              unifyVar sub nf′′ b >>= λ sub → 
                              unifyNfAgainstNe sub (neu ne′) ne inc
      ; _ → nothing })
    (b isIn? sub)
  unifyNfAgainstNe sub (neu (app ne₁ nf₁)) (app ne₂ nf₂) inc =
    thiningsNf inc nf₁            >>= λ nf₁′ →
    unifyNfAgainstNf sub nf₁′ nf₂ >>= λ sub →
    unifyNfAgainstNe sub (neu ne₁) ne₂ inc
  unifyNfAgainstNe sub nf (app ne arg) inc = nothing

  unifyVar : {A B : Set} {n : ℕ} (sub : Subst A B n) → Nf A → B → Maybe (Subst A B n)
  unifyVar base           nf                  b        = dec (eq nf (neu $ var b)) (const $ just base) (const nothing)
  unifyVar (meta sub)     nf                  nothing  = just (bind nf sub)
  unifyVar (bind nf₁ sub) nf₂                 nothing  = dec (eq nf₁ nf₂) (const $ just (bind nf₁ sub)) (const nothing)
  unifyVar (same sub)     (neu (var nothing)) nothing  = just (same sub)
  unifyVar (same sub)     nf                  nothing  = nothing
  unifyVar (meta sub)     nf                  (just b) = meta     <$> unifyVar sub nf b
  unifyVar (bind nf₁ sub) nf₂                 (just b) = bind nf₁ <$> unifyVar sub nf₂ b
  unifyVar (same sub)     nf                  (just b) = thiningNf z nf >>= λ ne → same <$> unifyVar sub ne b

open import Data.Empty

init : {A : Set} (pr : ⊥ ⊆′ A) → Subst ⊥ A 0
init refl       = base
init (step inc) = meta (init inc)

test : Maybe $ Subst ⊥ (Maybe (Maybe ⊥)) 0
test = unifyNfAgainstNf (init (step (step refl))) `λfλx→2 patt

  where

    `λfλx→2 : Nf ⊥
    `λfλx→2 = lam $ lam $ suc (suc zro)

    patt : Nf (Maybe (Maybe ⊥))
    patt = lam $ lam $ neu $ app (var (just (just nothing))) (nvar nothing)




