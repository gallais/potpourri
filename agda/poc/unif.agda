{-# OPTIONS --type-in-type                #-}
{-# OPTIONS --injective-type-constructors #-}

module unif where

open import Data.Fin
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Maybe
open import Function as F hiding (_∋_)
open import Category.Monad

module MM = RawMonad   (monad   {_})
open MM

open import Relation.Nullary
open import lib.Nullary
open import Relation.Binary.PropositionalEquality

--postulate
--  eq : {A : Set} (a b : A) → Dec (a ≡ b)

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
  zro : ∀ {A} → Maybe A ∋ nothing
  suc : ∀ {A a} → A ∋ a → Maybe A ∋ just a

infix 5 _─_
_─_ : ∀ A {a} → A ∋ a → Set
._ ─ zro {A}   = A
._ ─ suc {A} v = Maybe $ A ─ v

mutual

  data Nf (A : Set) : Set where
    lam : Nf (Maybe A) → Nf A
    zro : Nf A
    suc : Nf A → Nf A
    neu : (ne : Ne A) → Nf A

  data Ne (A : Set) : Set where
    var : (a : A) → Ne A
    app : Ne A → (nf : Nf A) → Ne A
    rec : (s : Nf A) (z : Nf A) (n : Ne A) → Ne A

just-inj : {B : Set} {a b : B} (eq : (Maybe B F.∋ just a) ≡ just b) → a ≡ b
just-inj refl = refl

eqMaybe : {B : Set} (eq : (a b : B) → Dec (a ≡ b)) → (a b : Maybe B) → Dec (a ≡ b)
eqMaybe eq (just a) (just b) = dec (eq a b) (yes ∘ cong just) (λ ¬eq → no $ ¬eq ∘ just-inj)
eqMaybe eq (just a) nothing  = no (λ ())
eqMaybe eq nothing  (just b) = no (λ ())
eqMaybe eq nothing  nothing  = yes refl

eqMaybe⁻¹ : {B : Set} (eq : (a b : Maybe B) → Dec (a ≡ b)) → (a b : B) → Dec (a ≡ b)
eqMaybe⁻¹ eq a b = dec (eq (just a) (just b)) (yes ∘ just-inj) (λ ¬eq → no $ ¬eq ∘ cong just)

var-inj : {A : Set} {a b : A} → var a ≡ var b → a ≡ b
var-inj refl = refl

lam-inj : {A : Set} {a b : Nf (Maybe A)} → lam a ≡ lam b → a ≡ b
lam-inj refl = refl

suc-inj : {A : Set} {a b : Nf A} → _≡_ {A = Nf A} (suc a) (suc b) → a ≡ b
suc-inj refl = refl

neu-inj : {A : Set} {a b : Ne A} → neu a ≡ neu b → a ≡ b
neu-inj refl = refl

app-inj : {A : Set} {a b : Ne A} {c d : Nf A} → app a c ≡ app b d → a ≡ b × c ≡ d
app-inj refl = refl , refl

rec-inj : {A : Set} {a b : Ne A} {c d e f : Nf A} → rec c d a ≡ rec e f b → c ≡ e × d ≡ f × a ≡ b
rec-inj refl = refl , refl , refl

mutual

  eqNf : {A : Set} (eq : (a b : A) → Dec (a ≡ b)) → (a b : Nf A) → Dec (a ≡ b)
  eqNf eq (lam a) (lam b) = dec (eqNf (eqMaybe eq) a b) (yes ∘ cong lam) (λ ¬eq → no $ ¬eq ∘ lam-inj)
  eqNf eq (lam a) zro = no (λ ())
  eqNf eq (lam a) (suc b) = no (λ ())
  eqNf eq (lam a) (neu ne) = no (λ ())
  eqNf eq zro (lam b) = no (λ ())
  eqNf eq zro zro = yes refl
  eqNf eq zro (suc b) = no (λ ())
  eqNf eq zro (neu ne) = no (λ ())
  eqNf eq (suc a) (lam b) = no (λ ())
  eqNf eq (suc a) zro = no (λ ())
  eqNf eq (suc a) (suc b) = dec (eqNf eq a b) (yes ∘ cong suc) (λ ¬eq → no $ ¬eq ∘ suc-inj)
  eqNf eq (suc a) (neu ne) = no (λ ())
  eqNf eq (neu ne) (lam b) = no (λ ())
  eqNf eq (neu ne) zro = no (λ ())
  eqNf eq (neu ne) (suc b) = no (λ ())
  eqNf eq (neu ne) (neu ne₁) = dec (eqNe eq ne ne₁) (yes ∘ cong neu) (λ ¬eq → no $ ¬eq ∘ neu-inj)

  eqNe : {A : Set} (eq : (a b : A) → Dec (a ≡ b)) → (a b : Ne A) → Dec (a ≡ b)
  eqNe eq (var a) (var a₁) = dec (eq a a₁) (yes ∘ cong var) (λ ¬eq → no $ ¬eq ∘ var-inj)
  eqNe eq (var a) (app b nf) = no (λ ())
  eqNe eq (var a) (rec s z b) = no (λ ())
  eqNe eq (app a nf) (var a₁) = no (λ ())
  eqNe eq (app a nf) (app b nf₁) =
    dec (eqNe eq a b) (λ eqab →
    dec (eqNf eq nf nf₁) (λ eqnfnf₁ → yes $ cong₂ app eqab eqnfnf₁)
      (λ ¬eq → no $ ¬eq ∘ proj₂ ∘ app-inj))
      (λ ¬eq → no $ ¬eq ∘ proj₁ ∘ app-inj)
  eqNe eq (app a nf) (rec s z b) = no (λ ())
  eqNe eq (rec s z a) (var a₁) = no (λ ())
  eqNe eq (rec s z a) (app b nf) = no (λ ())
  eqNe eq (rec s z a) (rec s₁ z₁ b) =
    dec (eqNf eq s s₁) (λ eqss₁ →
    dec (eqNf eq z z₁) (λ eqzz₁ →
    dec (eqNe eq a b)  (λ eqab  → yes $ trans (cong₂ (rec s) eqzz₁ eqab) (cong (λ s → rec s z₁ b) eqss₁))
      (λ ¬eq → no $ ¬eq ∘ proj₂ ∘ proj₂ ∘ rec-inj))
      (λ ¬eq → no $ ¬eq ∘ proj₁ ∘ proj₂ ∘ rec-inj))
      (λ ¬eq → no $ ¬eq ∘ proj₁ ∘ rec-inj)

eq⊆′ : {A B : Set} (eq : (a b : B) → Dec (a ≡ b)) (inc : A ⊆′ B) → (a b : A) → Dec (a ≡ b)
eq⊆′ eq refl       = eq
eq⊆′ eq (step inc) = eq⊆′ (eqMaybe⁻¹ eq) inc

eq⊆′⁻¹ : {A B : Set} (eq : (a b : A) → Dec (a ≡ b)) (inc : A ⊆′ B) → (a b : B) → Dec (a ≡ b)
eq⊆′⁻¹ eq refl       = eq
eq⊆′⁻¹ eq (step inc) = eqMaybe $ eq⊆′⁻¹ eq inc

mutual

  mapNf : {A B : Set} (f : A → B) → Nf A → Nf B
  mapNf f (lam nf) = lam $ mapNf (maybe (just ∘ f) nothing) nf
  mapNf f zro      = zro
  mapNf f (suc nf) = suc $ mapNf f nf
  mapNf f (neu ne) = neu $ mapNe f ne

  mapNe : {A B : Set} (f : A → B) → Ne A → Ne B
  mapNe f (var a)      = var $ f a
  mapNe f (app ne nf)  = app (mapNe f ne) (mapNf f nf)
  mapNe f (rec s z ne) = rec (mapNf f s) (mapNf f z) (mapNe f ne)

wkNf : {A : Set} → Nf A → Nf (Maybe A)
wkNf = mapNf just

wkNe : {A : Set} → Ne A → Ne (Maybe A)
wkNe = mapNe just

thining : ∀ {A a} (v : A ∋ a) → A → Maybe (A ─ v)
thining zro     w = w
thining (suc v) w = maybe (map just ∘ thining v) nothing w

wk∋ : ∀ {A B a} (le : A ⊆ B) (v : A ∋ a) → B ∋ wk le a
wk∋ refl      v       = v
wk∋ (pop! le) zro     = zro
wk∋ (pop! le) (suc v) = suc $ wk∋ le v
wk∋ (step le) v       = suc $ wk∋ le v

mutual

  thiningNf : ∀ {A a} (v : A ∋ a) → Nf A → Maybe (Nf $ A ─ v)
  thiningNf v (lam nf) = map lam $ thiningNf (suc v) nf
  thiningNf v zro      = just zro
  thiningNf v (suc nf) = map suc $ thiningNf v nf
  thiningNf v (neu ne) = map neu $ thiningNe v ne

  thiningNe : ∀ {A a} (v : A ∋ a) → Ne A → Maybe (Ne $ A ─ v)
  thiningNe v (var w)      = map var $ thining v w
  thiningNe v (app ne nf)  =
    maybe (λ ne′ → map (app ne′) $ thiningNf v nf) nothing (thiningNe v ne)
  thiningNe v (rec s z ne) = rec <$> thiningNf v s ⊛ thiningNf v z ⊛ thiningNe v ne 

thiningsNf : {A B : Set} (inc : A ⊆′ B) → Nf B → Maybe (Nf A)
thiningsNf refl       nf = just nf
thiningsNf (step inc) nf = thiningNf zro nf >>= thiningsNf inc

data Subst : (A B : Set) → ℕ → Set where
  base : ∀ {A} → Subst A A 0
  meta : ∀ {A B} → Subst A B 0 → Subst A (Maybe B) 0
  bind : ∀ {A B} → Nf A → Subst A B 0 → Subst A (Maybe B) 0
  same : ∀ {A B n} → Subst A B n → Subst (Maybe A) (Maybe B) (suc n)

eqSubst⁻¹ : {A B : Set} {n : ℕ} (eq : (a b : B) → Dec (a ≡ b)) (sub : Subst A B n) →
            (a b : A) → Dec (a ≡ b)
eqSubst⁻¹ eq base         = eq
eqSubst⁻¹ eq (meta sub)   = eqSubst⁻¹ (eqMaybe⁻¹ eq) sub
eqSubst⁻¹ eq (bind x sub) = eqSubst⁻¹ (eqMaybe⁻¹ eq) sub
eqSubst⁻¹ eq (same sub)   = eqMaybe $ eqSubst⁻¹ (eqMaybe⁻¹ eq) sub

unSame : ∀ {A B n} → Subst (Maybe A) (Maybe B) (suc n) → Subst A B n
unSame (same sub) = sub

var0 : ∀ {A} → Nf (Maybe A)
var0 = neu $ var nothing

pattern nvar b = neu (var b)

abst : {A B : Set} → A ⊆′ B → Nf B → Nf A
abst refl       nf = nf
abst (step inc) nf = abst inc (lam nf)

abstIn : ∀ {B : Set} (eq : (a b : B) → Dec (a ≡ b)) → Nf B → B → Nf (Maybe B)
abstIn eq nf v = mapNf (λ w → dec (eq v w) (const nothing) (const $ just w)) nf

infix 3 _isIn?_
_isIn?_ : {A B : Set} {n : ℕ} (b : B) (sub : Subst A B n) → Maybe A
b  isIn? base       = just b
mb isIn? meta sub   = mb >>= λ b → b isIn? sub
mb isIn? bind x sub = mb >>= λ b → b isIn? sub
mb isIn? same sub   = maybe (λ b → just <$> (b isIn? sub)) (just nothing) mb

mutual

  unifyNfAgainstNf : ∀ {A B : Set} (eq :  (a b : B) → Dec (a ≡ b)) {n : ℕ} (sub : Subst A B n) → Nf A → Nf B → Maybe (Subst A B n)
  -- go through constructors
  unifyNfAgainstNf eq sub (lam nf) (lam nf') = unSame <$> unifyNfAgainstNf (eqMaybe eq) (same sub) nf nf'
  unifyNfAgainstNf eq sub zro      zro       = return sub
  unifyNfAgainstNf eq sub (suc nf) (suc nf') = unifyNfAgainstNf eq sub nf nf'
  -- unify neutrals
  unifyNfAgainstNf eq sub nf       (neu ne)  = unifyNfAgainstNe eq sub nf ne refl
  -- spelling out all the ways in which it can fail
  unifyNfAgainstNf _  _   (lam _)  zro       = nothing
  unifyNfAgainstNf _  _   zro      (lam _)   = nothing
  unifyNfAgainstNf _  _   (lam _)  (suc _)   = nothing
  unifyNfAgainstNf _  _   (suc _)  (lam _)   = nothing
  unifyNfAgainstNf _  _   (suc _)  zro       = nothing
  unifyNfAgainstNf _  _   zro      (suc _)   = nothing
  unifyNfAgainstNf _  _   (neu _)  (lam _)   = nothing
  unifyNfAgainstNf _  _   (neu _)  zro       = nothing
  unifyNfAgainstNf _  _   (neu _)  (suc _)   = nothing

  unifyNfAgainstNe : ∀ {A B C : Set} eq {n : ℕ} (sub : Subst A B n) → Nf C → Ne B → (A ⊆′ C) → Maybe (Subst A B n)
  -- binding
  unifyNfAgainstNe eq sub nf (var v)           inc = unifyVar eq sub (abst inc nf) v
  -- abstracting
  unifyNfAgainstNe eq sub nf (app ne (nvar b)) inc =
    maybe (λ a → unifyNfAgainstNe eq sub (abstIn (eq⊆′⁻¹ (eqSubst⁻¹ eq sub) inc) nf (wk′ inc a)) ne (step inc))
    (case nf of λ
      { (neu (app ne′ nf′)) → thiningsNf inc nf      >>= λ nf′′ →
                              unifyVar eq sub nf′′ b >>= λ sub′ → 
                              unifyNfAgainstNe eq sub′ (neu ne′) ne inc
      ; _ → nothing })
    (b isIn? sub)
  unifyNfAgainstNe eq sub (neu (rec s₁ z₁ ne₁))  (rec s₂ z₂ ne₂) inc =
    thiningsNf inc s₁            >>= λ s₁′   →
    thiningsNf inc z₁            >>= λ z₁′   →
    unifyNfAgainstNf eq sub s₁′ s₂  >>= λ sub′  →
    unifyNfAgainstNf eq sub′ z₁′ z₂ >>= λ sub′′ →
    unifyNfAgainstNe eq sub′′ (neu ne₁) ne₂ inc 
  unifyNfAgainstNe eq sub (neu (app ne₁ nf₁)) (app ne₂ nf₂) inc =
    thiningsNf inc nf₁            >>= λ nf₁′ →
    unifyNfAgainstNf eq sub nf₁′ nf₂ >>= λ sub′ →
    unifyNfAgainstNe eq sub′ (neu ne₁) ne₂ inc
  unifyNfAgainstNe eq sub nf (app ne arg) inc = nothing
  unifyNfAgainstNe eq sub nf (rec s z ne) inc = nothing

  unifyVar : ∀ {A B : Set} eq {n : ℕ} (sub : Subst A B n) → Nf A → B → Maybe (Subst A B n)
  unifyVar eq base           nf                  b        = dec (eqNf eq nf (nvar b)) (const $ just base) (const nothing)
  unifyVar eq (meta sub)     nf                  nothing  = just (bind nf sub)
  unifyVar eq (bind nf₁ sub) nf₂                 nothing  = dec (eqNf (eqSubst⁻¹ eq (meta sub)) nf₁ nf₂) (const $ just (bind nf₁ sub)) (const nothing)
  unifyVar eq (same sub)     (neu (var nothing)) nothing  = just (same sub)
  unifyVar eq (same sub)     nf                  nothing  = nothing
  unifyVar eq (meta sub)     nf                  (just b) = meta     <$> unifyVar (eqMaybe⁻¹ eq) sub nf b
  unifyVar eq (bind nf₁ sub) nf₂                 (just b) = bind nf₁ <$> unifyVar (eqMaybe⁻¹ eq) sub nf₂ b
  unifyVar eq (same sub)     nf                  (just b) = thiningNf zro nf >>= λ ne → same <$> unifyVar (eqMaybe⁻¹ eq) sub ne b

open import Data.Empty

init : {A B : Set} (pr : A ⊆′ B) → Subst A B 0
init refl       = base
init (step inc) = meta (init inc)

open import Data.List

test : List $ Maybe $ Subst (Maybe ⊥) (Maybe (Maybe (Maybe (Maybe ⊥)))) 0
test = unifyNfAgainstNf (eq⊆′⁻¹ (eqMaybe (λ ())) inc) sub `λfλx→2 patt₁
     ∷ unifyNfAgainstNf (eq⊆′⁻¹ (eqMaybe (λ ())) inc) sub `x+x+x  patt₂
     ∷ unifyNfAgainstNf (eq⊆′⁻¹ (eqMaybe (λ ())) inc) sub `x+x+x  patt₃
     ∷ []

  where

    A : Set
    A = Maybe ⊥

    B : Set
    B = Maybe $ Maybe $ Maybe $ Maybe ⊥

    inc : A ⊆′ B
    inc = step (step (step refl))

    sub : Subst A B 0
    sub = init inc

    `λfλx→2 : Nf A
    `λfλx→2 = lam $ lam $ suc (suc zro)

    patt₁ : Nf B
    patt₁ = lam $ lam $ neu $ app (app (var (just (just nothing))) (nvar nothing)) (nvar (just nothing))

    plus : {A : Set} → Nf A → Ne A → Ne A
    plus x y = rec (lam $ suc (nvar nothing)) x y

    `x+x+x : Nf A
    `x+x+x = let x = var nothing in neu $ plus (neu $ plus (neu x) x) x

    patt₂ : Nf B
    patt₂ = neu $ plus (neu $ plus (nvar nothing) (var (just nothing))) (var (just (just nothing)))

    patt₃ : Nf B
    patt₃ = neu $ plus (nvar nothing) (var (just nothing)) 

