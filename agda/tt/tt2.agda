{-# OPTIONS --no-positivity-check #-}

module tt.tt2 where

open import Data.Nat as ℕ
open import Data.Fin
open import Data.Product
open import Function

open import tt.env

record Domain : Set₁ where
  field
    Var : ℕ → Set
    Chk : ℕ → Set
    Inf : ℕ → Set
    Abs : ℕ → Set
open Domain

record [_]_⇒[_]_ (S : Domain) (m : ℕ) (T : Domain) (n : ℕ) : Set where
  field
    fVar : Var S m → Var T n
    fChk : Chk S m → Chk T n
    fInf : Inf S m → Inf T n
    fAbs : Abs S m → Abs T n
open [_]_⇒[_]_

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

fmap-CheckF : {S T : Domain} {m n : ℕ} → [ S ] m ⇒[ T ] n → CheckF S m → CheckF T n
fmap-CheckF f (`sig A B) = `sig (fChk f A) (fAbs f B)
fmap-CheckF f (`pi A B)  = `pi (fChk f A) (fAbs f B)
fmap-CheckF f `nat       = `nat
fmap-CheckF f `set       = `set
fmap-CheckF f (`lam t)   = `lam (fAbs f t)
fmap-CheckF f (`per a b) = `per (fChk f a) (fChk f b)
fmap-CheckF f `zro       = `zro
fmap-CheckF f (`suc m)   = `suc (fChk f m)
fmap-CheckF f (`emb e)   = `emb (fInf f e)

fmap-InferF : {S T : Domain} {m n : ℕ} → [ S ] m ⇒[ T ] n → InferF S m → InferF T n
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

check : {n : ℕ} → Check n → CheckF language n
check (mkCheck t) = t

infer : {n : ℕ} → Infer n → InferF language n
infer (mkInfer t) = t

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

  _⊨evalC_ = λ {n} c → lemma-Check {n} c diag
  _⊨evalI_ = λ {n} i → lemma-Infer {n} i diag

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
  
    reify : {n : ℕ} → [ record language { Abs = Kripke Fin Check } ] n ⇒[ language ] n
    reify = record { fVar = id; fChk = id; fInf = id
                   ; fAbs = λ t → t extend zero }
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
  ; ⟦check⟧ = mkCheck ∘ λ
                { (`sig A B)  → `sig A (abs′ (λ {n} → B {n}))
                ; (`pi A B)   → `pi  A (abs′ (λ {n} → B {n}))
                ; `nat        → `nat
                ; `set        → `set
                ; (`lam b)    → `lam (abs′ (λ {n} → b {n}))
                ; (`per a b)  → `per a b
                ; `zro        → `zro
                ; (`suc m)    → `suc m
                ; (`emb e)    → `emb e }
  ; ⟦infer⟧ = mkInfer ∘ λ
                { (`var k)        → infer k
                ; (`ann t A)      → `ann t A
                ; (`app t u)      → `app t u
                ; (`fst t)        → `fst t
                ; (`snd t)        → `snd t
                ; (`ind p z s m)  → `ind p z s m }

  } where

  var₀ : {n : ℕ} → Infer (suc n)
  var₀ = mkInfer $ `var zero

  abs′ : {n : ℕ} → Kripke Infer Check n → Check (suc n)
  abs′ {n} = abs {n = n} (mkInfer $ `var zero)

substI : {m n : ℕ} → Infer m → Var m =>[ Infer ] n → Infer n
substI = Substitution ⊨⟦_⟧I_

substC : {m n : ℕ} → Check m → Var m =>[ Infer ] n → Check n
substC = Substitution ⊨⟦_⟧C_

mutual

  data Model (n : ℕ) : Set where
    Error :                  Model n
    Stuck : InferF model n → Model n
    Value : CheckF model n → Model n

  model : Domain
  model = record
    { Var = Fin
    ; Chk = Model
    ; Inf = Model
    ; Abs = Kripke Model Model }

mutual

  {-# TERMINATING #-}
  weakM : Weakening Model
  weakM ren Error       = Error
  weakM ren (Stuck ne)  = Stuck (fmap-InferF (weakM′ ren) ne)
  weakM ren (Value nf)  = Value (fmap-CheckF (weakM′ ren) nf)

  weakM′ : {m n : ℕ} → m ⊆ n → [ model ] m ⇒[ model ] n
  weakM′ ren = record
    { fVar = lookup ren
    ; fChk = weakM ren
    ; fInf = weakM ren
    ; fAbs = λ t ren′ → t (trans ren ren′)  }

Normalisation : Semantics Model Model Model
Normalisation = record
  { ⟦wk⟧    = weakM
  ; ⟦new⟧   = Stuck (`var zero)
  ; ⟦check⟧ = λ { (`sig A B)  → ⟦sig⟧ A B
                ; (`pi A B)   → ⟦pi⟧ A B
                ; `nat        → Value `nat
                ; `set        → Value `set
                ; (`lam b)    → Value $ `lam b
                ; (`per a b)  → ⟦per⟧ a b
                ; `zro        → Value `zro
                ; (`suc m)    → ⟦suc⟧ m
                ; (`emb e)    → ⟦emb⟧ e }
  ; ⟦infer⟧ = λ { (`var k)        → k
                ; (`ann t A)      → t
                ; (`app t u)      → ⟦app⟧ t u
                ; (`fst t)        → ⟦fst⟧ t
                ; (`snd t)        → ⟦snd⟧ t
                ; (`ind p z s m)  → ⟦ind⟧ p z s m } } where

  ⟦sig⟧ : {n : ℕ} → Model n → Kripke Model Model n → Model n
  ⟦sig⟧ Error  B = Error
  ⟦sig⟧ A      B = Value $ `sig A B
  
  ⟦pi⟧ : {n : ℕ} → Model n → Kripke Model Model n → Model n
  ⟦pi⟧ Error B = Error
  ⟦pi⟧ A     B = Value $ `pi A B
  
  ⟦per⟧ : {n : ℕ} → Model n → Model n → Model n
  ⟦per⟧ Error  B      = Error
  ⟦per⟧ A      Error  = Error
  ⟦per⟧ A      B      = Value $ `per A B
  
  ⟦suc⟧ : {n : ℕ} → Model n → Model n
  ⟦suc⟧ Error  = Error
  ⟦suc⟧ m      = Value $ `suc m

  ⟦emb⟧ : {n : ℕ} → Model n → Model n
  ⟦emb⟧ Error      = Error
  ⟦emb⟧ (Stuck ne) = Stuck ne
  ⟦emb⟧ (Value nf) = Value nf

  ⟦app⟧ : {n : ℕ} → Model n → Model n → Model n
  ⟦app⟧ Error              u = Error
  ⟦app⟧ (Stuck ne)         u = Stuck (`app (Stuck ne) u)
  ⟦app⟧ (Value (`pi A B))  u = B refl u
  ⟦app⟧ (Value (`lam b))   u = b refl u
  ⟦app⟧ _ _                  = Error

  ⟦fst⟧ : {n : ℕ} → Model n → Model n
  ⟦fst⟧ Error               = Error
  ⟦fst⟧ (Stuck ne)          = Stuck (`fst (Stuck ne))
  ⟦fst⟧ (Value (`per a b))  = a
  ⟦fst⟧ _                   = Error

  ⟦snd⟧ : {n : ℕ} → Model n → Model n
  ⟦snd⟧ Error               = Error
  ⟦snd⟧ (Stuck ne)          = Stuck (`snd (Stuck ne))
  ⟦snd⟧ (Value (`per a b))  = b
  ⟦snd⟧ _                   = Error

  ⟦ind⟧ : {n : ℕ} (p z s m : Model n) → Model n
  ⟦ind⟧ p z s Error             = Error
  ⟦ind⟧ p z s (Stuck ne)        = Stuck (`ind p z s (Stuck ne))
  ⟦ind⟧ p z s (Value `zro)      = z
  ⟦ind⟧ p z s (Value (`suc m))  = ⟦app⟧ (⟦app⟧ s m) (⟦ind⟧ p z s m)
  ⟦ind⟧ _ _ _ _                 = Error

import Level
open import Data.Maybe
open import Category.Monad
open RawMonad (monad {Level.zero})

mutual

  reifyIF : {n : ℕ} → Model n → Maybe (InferF language n)
  reifyIF (Stuck (`var k))       = return $ `var k
  reifyIF (Stuck (`ann t A))     =  `ann <$> reify t ⊛  reify A
  reifyIF (Stuck (`app t u))     = `app <$> reifyI t ⊛ reify u
  reifyIF (Stuck (`fst t))       = `fst <$> reifyI t
  reifyIF (Stuck (`snd t))       = `snd <$> reifyI t
  reifyIF (Stuck (`ind p z s m)) = `ind <$> reify p ⊛ reify z ⊛ reify z ⊛ reifyI m
  reifyIF _                      = nothing

  reifyI : {n : ℕ} → Model n → Maybe (Infer n)
  reifyI i = mkInfer <$> reifyIF i
  
  reifyCF : {n : ℕ} → Model n → Maybe (CheckF language n)
  reifyCF (Value (`sig A B)) = `sig <$> reify A ⊛ reifyAbs B
  reifyCF (Value (`pi A B))  = `pi <$> reify A ⊛ reifyAbs B
  reifyCF (Value `nat)       = return `nat
  reifyCF (Value `set)       = return `set
  reifyCF (Value (`lam t))   = `lam <$> reifyAbs t
  reifyCF (Value (`per a b)) = `per <$> reify a ⊛ reify b
  reifyCF (Value `zro)       = return `zro
  reifyCF (Value (`suc m))   = `suc <$> reify m
  reifyCF (Value (`emb e))   = check <$> reify e
  reifyCF _                  = nothing

  {-# TERMINATING #-}
  reifyAbs : {n : ℕ} → Kripke Model Model n → Maybe (Check (suc n))
  reifyAbs t = reify $ t extend (Stuck (`var zero))

  reifyC : {n : ℕ} → Model n → Maybe (Check n)
  reifyC c = mkCheck <$> reifyCF c
  
  reify : {n : ℕ} → Model n → Maybe (Check n)
  reify Error       = nothing
  reify (Stuck ne)  = mkCheck ∘ `emb <$> reifyI (Stuck ne)
  reify (Value nf)  = reifyC (Value nf)

normC : {n : ℕ} → Check n → Maybe (Check n)
normC = reify ∘ Normalisation ⊨evalC_

neu : {n : ℕ} → Infer n → Check n
neu ne = mkCheck (`emb ne)

var : (m : ℕ) {n : ℕ} (k : Fin n) → Infer (m ℕ.+ n)
var m k = mkInfer $ `var (raise m k)

nat : {n : ℕ} → Check n
nat = mkCheck `nat

zro : {n : ℕ} → Check n
zro = mkCheck `zro

set : {n : ℕ} → Check n
set = mkCheck `set

succ : {n : ℕ} → Check n → Check n
succ = mkCheck ∘ `suc

lam : {n : ℕ} (t : Fin (suc n) → Check (suc n)) → Check n
lam t = mkCheck $ `lam $ t zero

app : {n : ℕ} → Infer n → Check n → Infer n
app t u = mkInfer $ `app t u

ann : {n : ℕ} → Check n → Check n → Infer n
ann t A = mkInfer $ `ann t A

noLam : {n : ℕ} (t : Check n) → Check n
noLam t = mkCheck $ `lam $ weakC extend t

pi : {n : ℕ} (A : Check n) (B : Fin (suc n) → Check (suc n)) → Check n
pi A B = mkCheck $ `pi A $ B zero

arr : {n : ℕ} (A B : Check n) → Check n
arr A B = pi A (λ _ → weakC extend B)

sig : {n : ℕ} (A : Check n) (B : Fin (suc n) → Check (suc n)) → Check n
sig A B = mkCheck $ `sig A $ B zero

per : {n : ℕ} (a b : Check n) → Check n
per a b = mkCheck $ `per a b

prd : {n : ℕ} (A B : Check n) → Check n
prd A B = sig A (λ _ → weakC extend B)

_$′_ : {A B : Set} → (A → B) → A → B
_$′_ = _$_

embℕ : {n : ℕ} (m : ℕ) → Check n
embℕ zero    = mkCheck `zro
embℕ (suc m) = succ (embℕ m)

private

  addTy : {n : ℕ} → Check n
  addTy = arr nat nat

  add : Check 0
  add = lam $ λ m →
        lam $ λ n → neu $ mkInfer
            $ `ind (noLam nat)
                   (neu $ var 0 n)
                   (noLam $ lam $ λ m+n → succ $ neu $ var 0 zero)
                   (var 1 m)


  open import Relation.Binary.PropositionalEquality as PEq

  4+7 : normC (neu $ app (app (ann add addTy) (embℕ 4)) (embℕ 7)) ≡ just (embℕ 11)
  4+7 = PEq.refl

  vecTy : {n : ℕ} → Check n
  vecTy = arr set $ arr nat set

  vec : {n : ℕ} → Check n
  vec = lam $ λ A →
        lam $ λ n → neu $ mkInfer
            $ `ind (noLam set)
                   nat
                   (noLam $ lam $ λ vecAn → prd (neu $ var 2 A) (neu $ var 0 vecAn))
                   (var 0 n)

  vecSet3 : normC {0} (neu $ app (app (ann vec vecTy) set) (embℕ 3)) ≡ just (prd set $ prd set $ prd set nat)
  vecSet3 = PEq.refl

  tabTy : Check 0
  tabTy = pi set              $ λ A →
          arr (neu $ var 0 A) $
          pi nat              $ λ n →
          neu $ app (app (ann vec vecTy) (neu $ var 1 A)) (neu $ var 0 n)

  tab : Check 0
  tab = lam $ λ A →
        lam $ λ a →
        lam $ λ n → neu $ mkInfer
            $ `ind (neu $ app (ann vec vecTy) (neu $ var 2 A))
                   zro
                   (noLam $ lam $ λ tabn → per (neu $ var 2 a) (neu $ var 0 tabn))
                   (var 0 n)

  tabℕ3 : normC (neu $ app (app (app (ann tab tab) set) nat) (embℕ 3)) ≡ just (per nat $ per nat $ per nat zro)
  tabℕ3 = PEq.refl
