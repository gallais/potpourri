{-# OPTIONS --copatterns #-}

module tt2 where

open import Data.Nat
open import Data.Fin
open import Data.Product
open import Function

open import env

record Domain : Set₁ where
  field
    Var : ℕ → Set
    Chk : ℕ → Set
    Inf : ℕ → Set
    Abs : ℕ → Set
open Domain

_⇒_ : (X Y : ℕ → Set) → Set
X ⇒ Y = {n : ℕ} → X n → Y n

record _⇒D_ (S T : Domain) : Set where
  field
    fVar : Var S ⇒ Var T
    fChk : Chk S ⇒ Chk T
    fInf : Inf S ⇒ Inf T
    fAbs : Abs S ⇒ Abs T
open _⇒D_

data CheckF (S : Domain) (n : ℕ) : Set where
  -- types
  `sig : (A : Chk S n) (B : Abs S n) → CheckF S n
  `pi  : (A : Chk S n) (B : Abs S n) → CheckF S n
  `nat :                               CheckF S n
  `set :                               CheckF S n
  -- lambda abstraction
  `lam : (t : Abs S n)               → CheckF S n
  -- constructors
  `per : (a b : Chk S n)             → CheckF S n
  `zro :                               CheckF S n
  `suc : (m : Chk S n)               → CheckF S n
  -- embedding
  `emb : (e : Inf S n)               → CheckF S n

data InferF (S : Domain) (n : ℕ) : Set where
  -- head symbol
  `var : (k : Var S n)                   → InferF S n
  `ann : (t A : Chk S n)                 → InferF S n
  -- eliminators
  `app : (t : Inf S n) (u : Chk S n)     → InferF S n
  `fst : (t : Inf S n)                   → InferF S n
  `snd : (t : Inf S n)                   → InferF S n 
  `ind : (p z s : Chk S n) (m : Inf S n) → InferF S n

fmap-CheckF : {S T : Domain} → S ⇒D T → CheckF S ⇒ CheckF T
fmap-CheckF f (`sig A B) = `sig (fChk f A) (fAbs f B)
fmap-CheckF f (`pi A B)  = `pi (fChk f A) (fAbs f B)
fmap-CheckF f `nat       = `nat
fmap-CheckF f `set       = `set
fmap-CheckF f (`lam t)   = `lam (fAbs f t)
fmap-CheckF f (`per a b) = `per (fChk f a) (fChk f b)
fmap-CheckF f `zro       = `zro
fmap-CheckF f (`suc m)   = `suc (fChk f m)
fmap-CheckF f (`emb e)   = `emb (fInf f e)

fmap-InferF : {S T : Domain} → S ⇒D T → InferF S ⇒ InferF T
fmap-InferF f (`var k)       = `var (fVar f k)
fmap-InferF f (`ann t A)     = `ann (fChk f t) (fChk f A)
fmap-InferF f (`app t u)     = `app (fInf f t) (fChk f u)
fmap-InferF f (`fst t)       = `fst (fInf f t)
fmap-InferF f (`snd t)       = `snd (fInf f t)
fmap-InferF f (`ind p z s m) = `ind (fChk f p) (fChk f z) (fChk f s) (fInf f m)

mutual

  language : Domain
  language = record
    { Var = Fin
    ; Chk = Check
    ; Inf = Infer
    ; Abs = Check ∘ suc }

  data Check (n : ℕ) : Set where
    mkCheck : CheckF language n → Check n

  data Infer (n : ℕ) : Set where
    mkInfer : InferF language n → Infer n


record Semantics (E MC MI : ℕ → Set) : Set where

  meaning : Domain
  meaning = record
    { Var = E
    ; Chk = MC
    ; Inf = MI
    ; Abs = Kripke E MC }

  field
    -- Environment:
    ⟦wk⟧    : Weakening E
    ⟦new⟧   : E 1
    -- CheckF:
    ⟦check⟧ : {n : ℕ} → CheckF meaning n → MC n
    -- InferF:
    ⟦infer⟧ : {n : ℕ} → InferF meaning n → MI n

  fresh : {n : ℕ} → E (suc n)
  fresh = ⟦wk⟧ (eps ∙ zero) ⟦new⟧

  weakE : {m : ℕ} → Weakening $ Var m =>[ E ]_
  lookup (weakE inc ρ) k = ⟦wk⟧ inc $ lookup ρ k

  diag : {n : ℕ} → Var n =>[ E ] n
  diag {0}     = pack $ λ ()
  diag {suc _} = weakE extend diag ∙ fresh

module Eval {E MC MI : ℕ → Set} (Sem : Semantics E MC MI) where

  open Semantics Sem

  lemma-Check  : {m n : ℕ} → Check m → Var m =>[ E ] n → MC n
  lemma-Infer  : {m n : ℕ} → Infer m → Var m =>[ E ] n → MI n
  lemma-CheckF : {m n : ℕ} → CheckF language m → Var m =>[ E ] n → MC n
  lemma-InferF : {m n : ℕ} → InferF language m → Var m =>[ E ] n → MI n

  lemma-Check (mkCheck t) ρ = lemma-CheckF t ρ
  lemma-Infer (mkInfer t) ρ = lemma-InferF t ρ
  
  lemma-CheckF (`sig a b) ρ = ⟦check⟧ $ `sig (lemma-Check a ρ) (λ ren u → lemma-Check b (weakE ren ρ ∙ u))
  lemma-CheckF (`pi a b)  ρ = ⟦check⟧ $ `pi  (lemma-Check a ρ) (λ ren u → lemma-Check b (weakE ren ρ ∙ u))
  lemma-CheckF `nat       ρ = ⟦check⟧ `nat
  lemma-CheckF `set       ρ = ⟦check⟧ `set
  lemma-CheckF (`lam b)   ρ = ⟦check⟧ $ `lam (λ ren u → lemma-Check b (weakE ren ρ ∙ u))
  lemma-CheckF (`per a b) ρ = ⟦check⟧ $ `per (lemma-Check a ρ) $ lemma-Check b ρ
  lemma-CheckF `zro       ρ = ⟦check⟧ `zro
  lemma-CheckF (`suc m)   ρ = ⟦check⟧ $ `suc $ lemma-Check m ρ
  lemma-CheckF (`emb e)   ρ = ⟦check⟧ $ `emb $ lemma-Infer e ρ

  lemma-InferF (`var k)       ρ = ⟦infer⟧ $ `var $ lookup ρ k
  lemma-InferF (`ann t A)     ρ = ⟦infer⟧ $ `ann (lemma-Check t ρ) $ lemma-Check A ρ
  lemma-InferF (`app i u)     ρ = ⟦infer⟧ $ `app (lemma-Infer i ρ) $ lemma-Check u ρ
  lemma-InferF (`fst i)       ρ = ⟦infer⟧ $ `fst $ lemma-Infer i ρ
  lemma-InferF (`snd i)       ρ = ⟦infer⟧ $ `snd $ lemma-Infer i ρ
  lemma-InferF (`ind p z s i) ρ = ⟦infer⟧ $ `ind (lemma-Check p ρ) (lemma-Check z ρ) (lemma-Check s ρ)
                                          $ lemma-Infer i ρ

  _⊨⟦_⟧C_ = lemma-Check
  _⊨⟦_⟧I_ = lemma-Infer

  _⊨_⟨_/0⟩C : {n : ℕ} → Check (suc n) → E n → MC n
  _⊨_⟨_/0⟩C b u = lemma-Check b (diag ∙ u)

  _⊨_⟨_/0⟩I : {n : ℕ} → Infer (suc n) → E n → MI n
  _⊨_⟨_/0⟩I b u = lemma-Infer b (diag ∙ u)

open Eval hiding (lemma-CheckF ; lemma-InferF)

Renaming : Semantics Fin Check Infer
Renaming = record
  { ⟦wk⟧    = lookup
  ; ⟦new⟧   = zero
  ; ⟦check⟧ = mkCheck ∘ fmap-CheckF reify
  ; ⟦infer⟧ = mkInfer ∘ fmap-InferF reify }

  where
  
    reify : record language { Abs = Kripke Fin Check } ⇒D language
    reify = record { fVar = id; fChk = id; fInf = id
                   ; fAbs = λ t → t (step refl) zero }
weakI : Weakening Infer
weakI = flip $ Renaming ⊨⟦_⟧I_

weakC : Weakening Check
weakC = flip $ Renaming ⊨⟦_⟧C_

_`→_ : {n : ℕ} (a b : Check n) → Check n
a `→ b = mkCheck $ `pi a $ weakC extend b

Substitution : Semantics Infer Check Infer
Substitution = record
  { ⟦wk⟧    = weakI
  ; ⟦new⟧   = mkInfer $ `var zero
  ; ⟦check⟧ = {!!}
  ; ⟦infer⟧ = {!!} }



{-
record
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

substI : {m n : ℕ} → InferF m → m =[ InferF ]=> n → InferF n
substI = Substitution ⊨⟦_⟧I_

substC : {m n : ℕ} → CheckF m → m =[ InferF ]=> n → CheckF n
substC = Substitution ⊨⟦_⟧C_

ReduceABit : Semantics InferF CheckF InferF
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

  ann : {n : ℕ} (t A : CheckF n) → InferF n
  ann (`emb e) A = e
  ann t        A = `ann t A
  
  app : {n : ℕ} (i : InferF n) (t : CheckF n) → InferF n
  app (`ann (`lam t) (`pi a b)) u = Substitution ⊨ ann t b ⟨ ann u a /0⟩I
  app i                         u = `app i u
  
  emb : {n : ℕ} (i : InferF n) → CheckF n
  emb (`ann t A) = t
  emb i          = `emb i

  ind : {n : ℕ} (p z s : CheckF n) (m : InferF n) → InferF n
  ind p z s (`ann `zro     A) = ann z (emb $ app (ann p (`pi `nat `set)) z)
  ind p z s (`ann (`suc n) A) =
    let annP   = ann p $ `pi `nat `set
        wkAnnP = weakI extend annP
        var0   = emb $ `var zero
        typS   = `pi `nat $ emb (app wkAnnP var0) `→ emb (app wkAnnP $ `suc var0)
    in app (app (ann s typS) n) $ emb $ ind p z s (`ann n `nat)
  ind p z s i = `ind p z s i
-}
