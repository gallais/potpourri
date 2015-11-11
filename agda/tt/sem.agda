module tt.sem where

open import Data.Nat
open import Data.Fin
open import Function

open import tt.raw
open import tt.env

-----------------------------------------------------------
-- SEMANTICS
-----------------------------------------------------------

record Semantics (E MC MT MI : ℕ → Set) : Set where
  field
    -- Environment:
    ⟦wk⟧   : {n m : ℕ} → Var n =>[ Fin ] m → E n → E m
    ⟦new⟧  : E 1
    -- Type↔Check
    ⟦El⟧   : {n : ℕ} (A : MC n) → MT n
    ⟦unEl⟧ : {n : ℕ} (A : MT n) → MC n
    -- Check:
    ⟦sig⟧  : {n : ℕ} (a : MT n) (b : Kripke E MT n) → MT n
    ⟦pi⟧   : {n : ℕ} (a : MT n) (b : Kripke E MT n) → MT n
    ⟦nat⟧  : {n : ℕ} → MC n
    ⟦set⟧  : {n : ℕ} → ℕ → MC n
    ⟦lam⟧  : {n : ℕ} (t : Kripke E MC n) → MC n
    ⟦per⟧  : {n : ℕ} (a b : MC n) → MC n
    ⟦zro⟧  : {n : ℕ} → MC n
    ⟦suc⟧  : {n : ℕ} (m : MC n) → MC n
    ⟦emb⟧  : {n : ℕ} (e : MI n) → MC n
    -- Infer:
    ⟦var⟧  : {n : ℕ} (e : E n) → MI n
    ⟦ann⟧  : {n : ℕ} (t : MC n) (A : MT n) → MI n
    ⟦app⟧  : {n : ℕ} (t : MI n) (u : MC n) → MI n
    ⟦fst⟧  : {n : ℕ} (t : MI n) → MI n
    ⟦snd⟧  : {n : ℕ} (t : MI n) → MI n
    ⟦ind⟧  : {n : ℕ} (p z s : MC n) (m : MI n) → MI n

  fresh : {n : ℕ} → E (suc n)
  fresh = ⟦wk⟧ (eps ∙ zero) ⟦new⟧

  weakE : {m : ℕ} → Weakening $ Var m =>[ E ]_
  lookup (weakE inc ρ) k = ⟦wk⟧ inc $ lookup ρ k

  diag : {n : ℕ} → Var n =>[ E ] n
  diag {0}     = pack $ λ ()
  diag {suc _} = weakE extend diag ∙ fresh
  
module semantics {E MC MT MI : ℕ → Set} (Sem : Semantics E MC MT MI) where

  open Semantics Sem

  lemmaC : {m n : ℕ} → Check m → Var m =>[ E ] n → MC n
  lemmaT : {m n : ℕ} → Type m  → Var m =>[ E ] n → MT n
  lemmaI : {m n : ℕ} → Infer m → Var m =>[ E ] n → MI n

  lemmaC (`sig a b) ρ = ⟦unEl⟧ $ ⟦sig⟧ (lemmaT a ρ) $ λ inc u → lemmaT b $ weakE inc ρ ∙ u 
  lemmaC (`pi a b)  ρ = ⟦unEl⟧ $ ⟦pi⟧ (lemmaT a ρ)  $ λ inc u → lemmaT b $ weakE inc ρ ∙ u
  lemmaC `nat       ρ = ⟦nat⟧
  lemmaC (`set b)   ρ = ⟦set⟧ b
  lemmaC (`lam b)   ρ = ⟦lam⟧ λ inc u → lemmaC b $ weakE inc ρ ∙ u
  lemmaC (`per a b) ρ = ⟦per⟧ (lemmaC a ρ) $ lemmaC b ρ
  lemmaC `zro       ρ = ⟦zro⟧
  lemmaC (`suc m)   ρ = ⟦suc⟧ $ lemmaC m ρ
  lemmaC (`emb e)   ρ = ⟦emb⟧ $ lemmaI e ρ

  lemmaT A ρ = ⟦El⟧ (lemmaC (unEl A) ρ)

  lemmaI (`var k)       ρ = ⟦var⟧ $ lookup ρ k
  lemmaI (`ann t A)     ρ = ⟦ann⟧ (lemmaC t ρ) $ lemmaT A ρ
  lemmaI (`app i u)     ρ = ⟦app⟧ (lemmaI i ρ) $ lemmaC u ρ
  lemmaI (`fst i)       ρ = ⟦fst⟧ $ lemmaI i ρ
  lemmaI (`snd i)       ρ = ⟦snd⟧ $ lemmaI i ρ
  lemmaI (`ind p z s i) ρ = ⟦ind⟧ (lemmaC p ρ) (lemmaC z ρ) (lemmaC s ρ) $ lemmaI i ρ

  _⊨⟦_⟧C_ = lemmaC
  _⊨⟦_⟧T_ = lemmaT
  _⊨⟦_⟧I_ = lemmaI

  _⊨_⟨_/0⟩C : {n : ℕ} → Check (suc n) → E n → MC n
  _⊨_⟨_/0⟩C b u = lemmaC b (diag ∙ u)
  
  _⊨_⟨_/0⟩T : {n : ℕ} → Type (suc n) → E n → MT n
  _⊨_⟨_/0⟩T b u = lemmaT b (diag ∙ u)

  _⊨_⟨_/0⟩I : {n : ℕ} → Infer (suc n) → E n → MI n
  _⊨_⟨_/0⟩I b u = lemmaI b (diag ∙ u)

open semantics hiding (lemmaC ; lemmaT ; lemmaI) public



-----------------------------------------------------------
-- SYNTACTIC SEMANTICS
-----------------------------------------------------------

record Syntactic (E : ℕ → Set) : Set where
  field
    ⟦wk⟧  : Weakening E
    ⟦new⟧ : E 1
    ⟦var⟧ : {n : ℕ} → E n → Infer n

  fresh : {n : ℕ} → E (suc n)
  fresh = ⟦wk⟧ (eps ∙ zero) ⟦new⟧

module syntactic {E : ℕ → Set} (Syn : Syntactic E) where

  open Syntactic Syn

  lemma : Semantics E Check Type Infer
  lemma = record
    { ⟦wk⟧   = ⟦wk⟧
    ; ⟦new⟧  = ⟦new⟧
    ; ⟦El⟧   = El
    ; ⟦unEl⟧ = unEl
    ; ⟦sig⟧  = λ a → sig a ∘ abs fresh
    ; ⟦pi⟧   = λ a → pi a ∘ abs fresh
    ; ⟦nat⟧  = `nat
    ; ⟦set⟧  = `set
    ; ⟦lam⟧  = `lam ∘ abs fresh
    ; ⟦per⟧  = `per
    ; ⟦zro⟧  = `zro
    ; ⟦suc⟧  = `suc
    ; ⟦emb⟧  = `emb
    ; ⟦var⟧  = ⟦var⟧
    ; ⟦ann⟧  = `ann
    ; ⟦app⟧  = `app
    ; ⟦fst⟧  = `fst
    ; ⟦snd⟧  = `snd
    ; ⟦ind⟧  = `ind }



-----------------------------------------------------------
-- EXAMPLES OF SYNTACTIC SEMANTICS
-----------------------------------------------------------

Renaming : Semantics Fin Check Type Infer
Renaming = syntactic.lemma $ record
  { ⟦wk⟧  = lookup
  ; ⟦new⟧ = zero
  ; ⟦var⟧ = `var }

weakI : Weakening Infer
weakI = flip $ Renaming ⊨⟦_⟧I_

weakT : Weakening Type
weakT = flip $ Renaming ⊨⟦_⟧T_

weakC : Weakening Check
weakC = flip $ Renaming ⊨⟦_⟧C_

Substitution : Semantics Infer Check Type Infer
Substitution = syntactic.lemma $ record
  { ⟦wk⟧  = weakI
  ; ⟦new⟧ = `var zero
  ; ⟦var⟧ = id }

substI : Substituting Infer Infer
substI = Substitution ⊨⟦_⟧I_

substT : Substituting Infer Type
substT = Substitution ⊨⟦_⟧T_

substC : Substituting Infer Check
substC = Substitution ⊨⟦_⟧C_
