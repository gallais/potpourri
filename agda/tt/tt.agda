{-# OPTIONS --copatterns #-}

module tt where

open import Data.Nat
open import Data.Fin
open import Function

mutual

  data Check (n : ℕ) : Set where
    -- types
    `sig : (t : Check n) (u : Check (suc n)) → Check n
    `pi  : (A : Check n) (B : Check (suc n)) → Check n
    `nat :                                     Check n
    `set :                                     Check n
    -- lambda abstraction
    `lam : (t : Check (suc n))               → Check n
    -- constructors
    `per : (a b : Check n)                   → Check n
    `zro :                                     Check n
    `suc : (m : Check n)                     → Check n
    -- embedding
    `emb : (e : Infer n)                     → Check n

  data Infer (n : ℕ) : Set where
    -- head symbol
    `var : (k : Fin n)                     → Infer n
    `ann : (t : Check n) (A : Check n)     → Infer n
    -- eliminators
    `app : (t : Infer n) (u : Check n)     → Infer n
    `fst : (t : Infer n)                   → Infer n
    `snd : (t : Infer n)                   → Infer n
    `ind : (p z s : Check n) (m : Infer n) → Infer n


record _=[_]=>_ (m : ℕ) (E : ℕ → Set) (n : ℕ) : Set where
  constructor pack
  field lookup : (k : Fin m) → E n
open _=[_]=>_

_⊆_ : (m n : ℕ) → Set
m ⊆ n = m =[ Fin ]=> n

eps : {n : ℕ} {E : ℕ → Set} → 0 =[ E ]=> n
lookup eps ()

_∙_ : {n m : ℕ} {E : ℕ → Set} (ρ : m =[ E ]=> n) (u : E n) →  suc m =[ E ]=> n
lookup (ρ ∙ u) = λ k → case k of λ { zero → u; (suc k) → lookup ρ k }

refl : {n : ℕ} → n ⊆ n
lookup refl = id

trans : {m n p : ℕ} → m ⊆ n → n ⊆ p → m ⊆ p
lookup (trans ρmn ρnp) = lookup ρnp ∘ lookup ρmn

step : {m n : ℕ} → m ⊆ n → m ⊆ suc n
lookup (step ρ) = suc ∘ lookup ρ

pop! : {m n : ℕ} → m ⊆ n → suc m ⊆ suc n
pop! ρ = step ρ ∙ zero

extend : {m : ℕ} → m ⊆ suc m
extend = step refl

record Semantics (E MC MI : ℕ → Set) : Set where
  field
    -- Environment:
    ⟦wk⟧  : {n m : ℕ} (inc : n =[ Fin ]=> m) → E n → E m
    ⟦new⟧ : E 1
    -- Check:
    ⟦sig⟧ : {n : ℕ} (a : MC n) (b : {m : ℕ} (inc : n =[ Fin ]=> m) (e : E m) → MC m) → MC n
    ⟦pi⟧  : {n : ℕ} (a : MC n) (b : {m : ℕ} (inc : n =[ Fin ]=> m) (e : E m) → MC m) → MC n
    ⟦nat⟧ : {n : ℕ} → MC n
    ⟦set⟧ : {n : ℕ} → MC n
    ⟦lam⟧ : {n : ℕ} (t : {m : ℕ} (inc : n =[ Fin ]=> m) (e : E m) → MC m) → MC n
    ⟦per⟧ : {n : ℕ} (a b : MC n) → MC n
    ⟦zro⟧ : {n : ℕ} → MC n
    ⟦suc⟧ : {n : ℕ} (m : MC n) → MC n
    ⟦emb⟧ : {n : ℕ} (e : MI n) → MC n
    -- Infer:
    ⟦var⟧ : {n : ℕ} (e : E n) → MI n
    ⟦ann⟧ : {n : ℕ} (t A : MC n) → MI n
    ⟦app⟧ : {n : ℕ} (t : MI n) (u : MC n) → MI n
    ⟦fst⟧ : {n : ℕ} (t : MI n) → MI n
    ⟦snd⟧ : {n : ℕ} (t : MI n) → MI n
    ⟦ind⟧ : {n : ℕ} (p z s : MC n) (m : MI n) → MI n

  fresh : {n : ℕ} → E (suc n)
  fresh = ⟦wk⟧ (eps ∙ zero) ⟦new⟧

  weakE : {n m p : ℕ} (inc : n =[ Fin ]=> p) (ρ : m =[ E ]=> n) → m =[ E ]=> p
  lookup (weakE inc ρ) k = ⟦wk⟧ inc $ lookup ρ k

  diag : {n : ℕ} → n =[ E ]=> n
  diag {0}     = pack $ λ ()
  diag {suc _} = weakE extend diag ∙ fresh
  
module Eval {E MC MI : ℕ → Set} (Sem : Semantics E MC MI) where

  open Semantics Sem

  lemmaC : {m n : ℕ} (c : Check m) (ρ : m =[ E ]=> n) → MC n
  lemmaI : {m n : ℕ} (i : Infer m) (ρ : m =[ E ]=> n) → MI n

  lemmaC (`sig a b) ρ = ⟦sig⟧ (lemmaC a ρ) $ λ inc u → lemmaC b $ weakE inc ρ ∙ u 
  lemmaC (`pi a b)  ρ = ⟦pi⟧ (lemmaC a ρ)  $ λ inc u → lemmaC b $ weakE inc ρ ∙ u
  lemmaC `nat       ρ = ⟦nat⟧
  lemmaC `set       ρ = ⟦set⟧
  lemmaC (`lam b)   ρ = ⟦lam⟧ λ inc u → lemmaC b $ weakE inc ρ ∙ u
  lemmaC (`per a b) ρ = ⟦per⟧ (lemmaC a ρ) $ lemmaC b ρ
  lemmaC `zro       ρ = ⟦zro⟧
  lemmaC (`suc m)   ρ = ⟦suc⟧ $ lemmaC m ρ
  lemmaC (`emb e)   ρ = ⟦emb⟧ $ lemmaI e ρ

  lemmaI (`var k)       ρ = ⟦var⟧ $ lookup ρ k
  lemmaI (`ann t A)     ρ = ⟦ann⟧ (lemmaC t ρ) $ lemmaC A ρ
  lemmaI (`app i u)     ρ = ⟦app⟧ (lemmaI i ρ) $ lemmaC u ρ
  lemmaI (`fst i)       ρ = ⟦fst⟧ $ lemmaI i ρ
  lemmaI (`snd i)       ρ = ⟦snd⟧ $ lemmaI i ρ
  lemmaI (`ind p z s i) ρ = ⟦ind⟧ (lemmaC p ρ) (lemmaC z ρ) (lemmaC s ρ) $ lemmaI i ρ

  _⊨⟦_⟧C_ = lemmaC
  _⊨⟦_⟧I_ = lemmaI

  _⊨_⟨_/0⟩C : {n : ℕ} (b : Check (suc n)) (u : E n) → MC n
  _⊨_⟨_/0⟩C b u = lemmaC b (diag ∙ u)

  _⊨_⟨_/0⟩I : {n : ℕ} (b : Infer (suc n)) (u : E n) → MI n
  _⊨_⟨_/0⟩I b u = lemmaI b (diag ∙ u)

open Eval hiding (lemmaC ; lemmaI)

Renaming : Semantics Fin Check Infer
Renaming = record
  { ⟦wk⟧  = lookup
  ; ⟦new⟧ = zero
  ; ⟦sig⟧ = λ a b → `sig a $ b extend zero
  ; ⟦pi⟧  = λ a b → `pi  a $ b extend zero
  ; ⟦nat⟧ = `nat
  ; ⟦set⟧ = `set
  ; ⟦lam⟧ = λ b   → `lam   $ b extend zero
  ; ⟦per⟧ = `per
  ; ⟦zro⟧ = `zro
  ; ⟦suc⟧ = `suc
  ; ⟦emb⟧ = `emb
  ; ⟦var⟧ = `var
  ; ⟦ann⟧ = `ann
  ; ⟦app⟧ = `app
  ; ⟦fst⟧ = `fst
  ; ⟦snd⟧ = `snd
  ; ⟦ind⟧ = `ind }

weakI : {m n : ℕ} (inc : m ⊆ n) (t : Infer m) → Infer n
weakI = flip $ Renaming ⊨⟦_⟧I_

weakC : {m n : ℕ} (inc : m ⊆ n) (t : Check m) → Check n
weakC = flip $ Renaming ⊨⟦_⟧C_

_`→_ : {n : ℕ} (a b : Check n) → Check n
a `→ b = `pi a $ weakC extend b

Substitution : Semantics Infer Check Infer
Substitution = record
  { ⟦wk⟧  = weakI
  ; ⟦new⟧ = `var zero
  ; ⟦sig⟧ = λ a b → `sig a $ b extend (`var zero)
  ; ⟦pi⟧  = λ a b → `pi  a $ b extend (`var zero)
  ; ⟦nat⟧ = `nat
  ; ⟦set⟧ = `set
  ; ⟦lam⟧ = λ b   → `lam   $ b extend (`var zero)
  ; ⟦per⟧ = `per
  ; ⟦zro⟧ = `zro
  ; ⟦suc⟧ = `suc
  ; ⟦emb⟧ = `emb
  ; ⟦var⟧ = id
  ; ⟦ann⟧ = `ann
  ; ⟦app⟧ = `app
  ; ⟦fst⟧ = `fst
  ; ⟦snd⟧ = `snd
  ; ⟦ind⟧ = `ind }

substI : {m n : ℕ} (t : Infer m) (ρ : m =[ Infer ]=> n) → Infer n
substI = Substitution ⊨⟦_⟧I_

substC : {m n : ℕ} (t : Check m) (ρ : m =[ Infer ]=> n) → Check n
substC = Substitution ⊨⟦_⟧C_

_⟨_/0⟩I : {n : ℕ} (b : Infer (suc n)) (u : Infer n) → Infer n
b ⟨ u /0⟩I = substI b (diag ∙ u) where open Semantics Substitution

_⟨_/0⟩C : {n : ℕ} (b : Check (suc n)) (u : Infer n) → Check n
b ⟨ u /0⟩C = substC b (diag ∙ u) where open Semantics Substitution

ReduceABit : Semantics Infer Check Infer
ReduceABit = record
  { ⟦wk⟧  = weakI
  ; ⟦new⟧ = `var zero
  ; ⟦sig⟧ = λ a b → `sig a $ b extend (`var zero)
  ; ⟦pi⟧  = λ a b → `pi  a $ b extend (`var zero)
  ; ⟦nat⟧ = `nat
  ; ⟦set⟧ = `set
  ; ⟦lam⟧ = λ b   → `lam   $ b extend (`var zero)
  ; ⟦per⟧ = `per
  ; ⟦zro⟧ = `zro
  ; ⟦suc⟧ = `suc
  ; ⟦emb⟧ = emb
  ; ⟦var⟧ = id
  ; ⟦ann⟧ = ann
  ; ⟦app⟧ = app
  ; ⟦fst⟧ = `fst
  ; ⟦snd⟧ = `snd
  ; ⟦ind⟧ = ind } where

  ann : {n : ℕ} (t A : Check n) → Infer n
  ann (`emb e) A = e
  ann t        A = `ann t A
  
  app : {n : ℕ} (i : Infer n) (t : Check n) → Infer n
  app (`ann (`lam t) (`pi a b)) u = Substitution ⊨ ann t b ⟨ ann u a /0⟩I
  app i                         u = `app i u
  
  emb : {n : ℕ} (i : Infer n) → Check n
  emb (`ann t A) = t
  emb i          = `emb i

  ind : {n : ℕ} (p z s : Check n) (m : Infer n) → Infer n
  ind p z s (`ann `zro     A) = ann z (emb $ app (ann p (`pi `nat `set)) z)
  ind p z s (`ann (`suc n) A) =
    let annP   = ann p $ `pi `nat `set
        wkAnnP = weakI extend annP
        var0   = emb $ `var zero
        typS   = `pi `nat $ emb (app wkAnnP var0) `→ emb (app wkAnnP $ `suc var0)
    in app (app (ann s typS) n) $ emb $ ind p z s (`ann n `nat)
  ind p z s i = `ind p z s i
