{-# OPTIONS --copatterns #-}

module tt where

open import Data.Nat as ℕ
open import Data.Fin hiding (_<_)
open import Function

mutual

  data Check (n : ℕ) : Set where
    -- types
    `sig : (t : Check n) (u : Check (suc n)) → Check n
    `pi  : (A : Check n) (B : Check (suc n)) → Check n
    `nat :                                     Check n
    `set : ℕ                                 → Check n
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


var₀ : {n : ℕ} → Check (suc n)
var₀ = `emb (`var zero)

record _=[_]=>_ (m : ℕ) (E : ℕ → Set) (n : ℕ) : Set where
  constructor pack
  field lookup : (k : Fin m) → E n
open _=[_]=>_

_⊆_ : (m n : ℕ) → Set
m ⊆ n = m =[ Fin ]=> n

Weakening : (X : ℕ → Set) → Set
Weakening X = {m n : ℕ} → m ⊆ n → X m → X n

eps : {n : ℕ} {E : ℕ → Set} → 0 =[ E ]=> n
lookup eps ()

_∙_ : {n m : ℕ} {E : ℕ → Set} → m =[ E ]=> n → E n →  suc m =[ E ]=> n
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

Kripke : (E M : ℕ → Set) (n : ℕ) → Set
Kripke E M n = {m : ℕ} → n ⊆ m → E m → M m

record Semantics (E MC MI : ℕ → Set) : Set where
  field
    -- Environment:
    ⟦wk⟧  : {n m : ℕ} → n =[ Fin ]=> m → E n → E m
    ⟦new⟧ : E 1
    -- Check:
    ⟦sig⟧ : {n : ℕ} (a : MC n) (b : Kripke E MC n) → MC n
    ⟦pi⟧  : {n : ℕ} (a : MC n) (b : Kripke E MC n) → MC n
    ⟦nat⟧ : {n : ℕ} → MC n
    ⟦set⟧ : {n : ℕ} → ℕ → MC n
    ⟦lam⟧ : {n : ℕ} (t : Kripke E MC n) → MC n
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

  weakE : {m : ℕ} → Weakening $ m =[ E ]=>_
  lookup (weakE inc ρ) k = ⟦wk⟧ inc $ lookup ρ k

  diag : {n : ℕ} → n =[ E ]=> n
  diag {0}     = pack $ λ ()
  diag {suc _} = weakE extend diag ∙ fresh
  
module Eval {E MC MI : ℕ → Set} (Sem : Semantics E MC MI) where

  open Semantics Sem

  lemmaC : {m n : ℕ} → Check m → m =[ E ]=> n → MC n
  lemmaI : {m n : ℕ} → Infer m → m =[ E ]=> n → MI n

  lemmaC (`sig a b) ρ = ⟦sig⟧ (lemmaC a ρ) $ λ inc u → lemmaC b $ weakE inc ρ ∙ u 
  lemmaC (`pi a b)  ρ = ⟦pi⟧ (lemmaC a ρ)  $ λ inc u → lemmaC b $ weakE inc ρ ∙ u
  lemmaC `nat       ρ = ⟦nat⟧
  lemmaC (`set b)   ρ = ⟦set⟧ b
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

  _⊨_⟨_/0⟩C : {n : ℕ} → Check (suc n) → E n → MC n
  _⊨_⟨_/0⟩C b u = lemmaC b (diag ∙ u)

  _⊨_⟨_/0⟩I : {n : ℕ} → Infer (suc n) → E n → MI n
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

weakI : Weakening Infer
weakI = flip $ Renaming ⊨⟦_⟧I_

weakC : Weakening Check
weakC = flip $ Renaming ⊨⟦_⟧C_

infixr 5 _`→_
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

substI : {m n : ℕ} → Infer m → m =[ Infer ]=> n → Infer n
substI = Substitution ⊨⟦_⟧I_

substC : {m n : ℕ} → Check m → m =[ Infer ]=> n → Check n
substC = Substitution ⊨⟦_⟧C_


Type : ℕ → Set
Type = Check

infixl 5 _∙⟩_
data Context : ℕ → Set where
  ⟨⟩    : Context 0
  _∙⟩_  : {n : ℕ} (Γ : Context n) (A : Type n) → Context (suc n)


postulate

  _↝_ : {n : ℕ} (a b : Check n) → Set
  admit : {n : ℕ} {a b : Check n} → a ↝ b

infix 1 _⊢_∋_ _⊢_∈_ _⊢var_∈_
mutual

  data _⊢_∋_ {n : ℕ} (Γ : Context n) : Type n → Check n → Set where

    `sig : {s : Check n} {t : Check (suc n)} {ℓ : ℕ} →

           Γ ⊢ `set ℓ ∋ s → Γ ∙⟩ s ⊢ `set ℓ ∋ t →
           --------------------------------------
           Γ ⊢ `set ℓ ∋ `sig s t

    `pi  : {s : Check n} {t : Check (suc n)} {ℓ : ℕ} →
  
           Γ ⊢ `set ℓ ∋ s → Γ ∙⟩ s ⊢ `set ℓ ∋ t →
           --------------------------------------
           Γ ⊢ `set ℓ ∋ `pi s t

    `nat : Γ ⊢ `set 0 ∋ `nat

    `set : {ℓ ℓ′ : ℕ} →

           ℓ > ℓ′ →
           --------------------
           Γ ⊢ `set ℓ ∋ `set ℓ′

    `lam : {b : Check (suc n)} {A : Type n} {B : Type (suc n)} →
    
           Γ ∙⟩ A ⊢ B ∋ b →
           --------------------
           Γ ⊢ `pi A B ∋ `lam b


    `per : {a b : Check n} {A : Type n} {B : Type (suc n)} →

           Γ ⊢ A ∋ a → Γ ⊢ Substitution ⊨ B ⟨ `ann a A /0⟩C ∋ b →
           -----------------------
           Γ ⊢ `sig A B ∋ `per a b

    `zro : Γ ⊢ `nat ∋ `zro

    `suc : {m : Check n} →

           Γ ⊢ `nat ∋ m →
           -----------------
           Γ ⊢ `nat ∋ `suc m

    `emb : {e : Infer n} {A : Type n} →

           Γ ⊢ e ∈ A →
           -----------
           Γ ⊢ A ∋ `emb e

    `red : {t : Check n} {A B : Type n} →

           A ↝ B → Γ ⊢ B ∋ t →
           ---------------------
           Γ ⊢ A ∋ t
         
  data _⊢var_∈_ : {n : ℕ} → Context n → Fin n → Type n → Set where

    zero : {n : ℕ} {Γ : Context n} {A : Type n} →

           ---------------------------------
           Γ ∙⟩ A ⊢var zero ∈ weakC extend A


    suc  : {n : ℕ} {Γ : Context n} {A B : Type n} {k : Fin n} →

           Γ ⊢var k ∈ B →
           ----------------------------------
           Γ ∙⟩ A ⊢var suc k ∈ weakC extend B


  data _⊢_∈_ {n : ℕ} (Γ : Context n) : Infer n → Type n → Set where
  
    `var : {k : Fin n} {A : Type n} →

           Γ ⊢var k ∈ A →
           --------------
           Γ ⊢ `var k ∈ A

    `ann : {t : Check n} {A : Type n} →

           Γ ⊢ A ∋ t →
           ----------------
           Γ ⊢ `ann t A ∈ A

    `app : {t : Infer n} {u : Check n} {A : Type n} {B : Type (suc n)} →

           Γ ⊢ t ∈ `pi A B → Γ ⊢ A ∋ u →
           -----------------------------
           Γ ⊢ `app t u ∈ Substitution ⊨ B ⟨ `ann u A /0⟩C

    `fst : {t : Infer n} {A : Type n} {B : Type (suc n)} →

           Γ ⊢  t ∈ `sig A B →
           -------------------
           Γ ⊢ `fst t ∈ A

    `snd : {t : Infer n} {A : Type n} {B : Type (suc n)} →

           Γ ⊢  t ∈ `sig A B →
           -------------------
           Γ ⊢ `snd t ∈ Substitution ⊨ B ⟨ `fst t /0⟩C

    `ind : {p z s : Check n} {m : Infer n} {ℓ : ℕ} →

           Γ ⊢ `pi `nat (`set ℓ) ∋ p →
           let P : {m : ℕ} → n ⊆ m → Check m → Check m
               P = λ inc x → `emb (`app (`ann (weakC inc p) (`pi `nat (`set ℓ))) x) in
           Γ ⊢ P refl `zro ∋ z →
           Γ ⊢ `pi `nat (P extend var₀ `→ P extend (`suc var₀)) ∋ s →
           Γ ⊢ m ∈ `nat →
           ---------------------------
           Γ ⊢ `ind p z s m ∈ P refl (`emb m)

    `red : {e : Infer n} {A B : Type n} →
           A ↝ B → Γ ⊢ e ∈ A →
           -------------------
           Γ ⊢ e ∈ B


infixr 0 _$′_
_$′_ : {A B : Set} → (A → B) → A → B
_$′_ = _$_

var : (m : ℕ) {n : ℕ} (k : Fin n) → Infer (m ℕ.+ n)
var m k = `var (raise m k)

var′ : (m : ℕ) {n : ℕ} (k : Fin n) → Check (m ℕ.+ n)
var′ m k = `emb (var m k)

lam : {n : ℕ} (t : Fin (suc n) → Check (suc n)) → Check n
lam t = `lam $ t zero

add : Check 0
add = lam $′ λ m →
      lam $′ λ n → `emb $′
      `ind (`lam `nat) (var′ 0 n) (`lam $′ lam $′ `suc ∘′ var′ 0) (var 1 m)

TypeCheckAdd : ⟨⟩ ⊢ `nat `→ `nat `→ `nat ∋ add
TypeCheckAdd =
  `lam $′
  `lam $′ `emb $′ `red prf $′
  `ind TypeCheckP TypeCheckVarN TypeCheckS $′ `var (suc zero)

  where

    p   = `lam `nat
    pTy : {n : ℕ} → Check n
    pTy = `pi `nat (`set 0)

    P : {m : ℕ} → 2 ⊆ m → Check m → Check m
    P = λ inc x → `emb (`app (`ann (weakC inc p) pTy) x)

    n   = var′ 0 zero
    nTy = P refl `zro

    TypeCheckVarN : _ ⊢ nTy ∋ n
    TypeCheckVarN = `red prf $′ `emb $′ `var zero
      where
        prf : nTy ↝ `nat
        prf = admit

    TypeCheckP : _ ⊢ pTy ∋ p
    TypeCheckP = `lam `nat

    s   = `lam $′ lam $′ `suc ∘′ var′ 0
    sTy = `pi `nat (P extend var₀ `→ P extend (`suc var₀))

    TypeCheckS : _ ⊢ sTy ∋ s
    TypeCheckS = `red prf $′ `lam $′ `lam $′ `suc $′ `emb $′ `var zero
      where
        prf : sTy ↝ `pi `nat (`nat `→ `nat)
        prf = admit
        

    prf : let P = `ann p pTy
              m = var′ 1 zero
          in `emb (`app P m) ↝ `nat
    prf = admit
