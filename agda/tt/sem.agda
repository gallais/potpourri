module tt.sem where

open import Data.Nat
open import Data.Fin hiding (lift)
open import Function

open import tt.raw
open import tt.red
open import tt.env

-----------------------------------------------------------
-- SEMANTICS
-----------------------------------------------------------

record Semantics (E MC MT MI : ℕ → Set) : Set where
  no-eta-equality
  field
    -- Environment:
    ⟦wk⟧   : {n m : ℕ} → Var n =>[ Fin ] m → E n → E m
    ⟦diag⟧ : {m : ℕ} → Var m =>[ E ] m
    -- Type
    ⟦sig⟧  : {n : ℕ} (a : MT n) (b : Kripke E MT n) → MT n
    ⟦pi⟧   : {n : ℕ} (a : MT n) (b : Kripke E MT n) → MT n
    ⟦nat⟧  : {n : ℕ} → MT n
    ⟦set⟧  : {n : ℕ} → ℕ → MT n
    ⟦elt⟧  : {n : ℕ} (e : MI n) → MT n
    -- Check
    ⟦lam⟧  : {n : ℕ} (t : Kripke E MC n) → MC n
    ⟦per⟧  : {n : ℕ} (a b : MC n) → MC n
    ⟦zro⟧  : {n : ℕ} → MC n
    ⟦suc⟧  : {n : ℕ} (m : MC n) → MC n
    ⟦typ⟧  : {n : ℕ} (e : MT n) → MC n
    ⟦emb⟧  : {n : ℕ} (e : MI n) → MC n
    -- Infer:
    ⟦var⟧  : {n : ℕ} (e : E n) → MI n
    ⟦ann⟧  : {n : ℕ} (t : MC n) (A : MT n) → MI n
    ⟦app⟧  : {n : ℕ} (t : MI n) (u : MC n) → MI n
    ⟦fst⟧  : {n : ℕ} (t : MI n) → MI n
    ⟦snd⟧  : {n : ℕ} (t : MI n) → MI n
    ⟦ind⟧  : {n : ℕ} (p : Kripke E MT n) (z s : MC n) (m : MI n) → MI n

  fresh : {n : ℕ} → E (suc n)
  fresh = lookup ⟦diag⟧ zero

  weakE : {m : ℕ} → Weakening $ Var m =>[ E ]_
  weakE = wk[ ⟦wk⟧ ]

  lift : {m n : ℕ} → Var m =>[ E ] n → Var suc m =>[ E ] suc n
  lift ρ = weakE extend ρ ∙ fresh

module semantics {E MC MT MI : ℕ → Set} (Sem : Semantics E MC MT MI) where

  open Semantics Sem

  lemmaC : {m n : ℕ} → Check m → Var m =>[ E ] n → MC n
  lemmaT : {m n : ℕ} → Type m  → Var m =>[ E ] n → MT n
  lemmaI : {m n : ℕ} → Infer m → Var m =>[ E ] n → MI n

  lemmaC (`lam b)   ρ = ⟦lam⟧ λ inc u → lemmaC b $ weakE inc ρ ∙ u
  lemmaC (`per a b) ρ = ⟦per⟧ (lemmaC a ρ) $ lemmaC b ρ
  lemmaC `zro       ρ = ⟦zro⟧
  lemmaC (`suc m)   ρ = ⟦suc⟧ $ lemmaC m ρ
  lemmaC (`typ A)   ρ = ⟦typ⟧ $ lemmaT A ρ
  lemmaC (`emb e)   ρ = ⟦emb⟧ $ lemmaI e ρ

  lemmaT (`sig a b) ρ = ⟦sig⟧ (lemmaT a ρ) $ λ inc u → lemmaT b $ weakE inc ρ ∙ u 
  lemmaT (`pi a b)  ρ = ⟦pi⟧ (lemmaT a ρ)  $ λ inc u → lemmaT b $ weakE inc ρ ∙ u
  lemmaT `nat       ρ = ⟦nat⟧
  lemmaT (`set b)   ρ = ⟦set⟧ b
  lemmaT (`elt e)   ρ = ⟦elt⟧ $ lemmaI e ρ

  lemmaI (`var k)       ρ = ⟦var⟧ $ lookup ρ k
  lemmaI (`ann t A)     ρ = ⟦ann⟧ (lemmaC t ρ) $ lemmaT A ρ
  lemmaI (`app i u)     ρ = ⟦app⟧ (lemmaI i ρ) $ lemmaC u ρ
  lemmaI (`fst i)       ρ = ⟦fst⟧ $ lemmaI i ρ
  lemmaI (`snd i)       ρ = ⟦snd⟧ $ lemmaI i ρ
  lemmaI (`ind p z s i) ρ = ⟦ind⟧ (λ inc u → lemmaT p $ weakE inc ρ ∙ u) (lemmaC z ρ) (lemmaC s ρ) $ lemmaI i ρ

  _⊨⟦_⟧C_ = lemmaC
  _⊨⟦_⟧T_ = lemmaT
  _⊨⟦_⟧I_ = lemmaI

  _⊨_⟨_/0⟩C : {n : ℕ} → Check (suc n) → E n → MC n
  _⊨_⟨_/0⟩C b u = lemmaC b (⟦diag⟧ ∙ u)
  
  _⊨_⟨_/0⟩T : {n : ℕ} → Type (suc n) → E n → MT n
  _⊨_⟨_/0⟩T b u = lemmaT b (⟦diag⟧ ∙ u)

  _⊨_⟨_/0⟩I : {n : ℕ} → Infer (suc n) → E n → MI n
  _⊨_⟨_/0⟩I b u = lemmaI b (⟦diag⟧ ∙ u)

open semantics hiding (lemmaC ; lemmaT ; lemmaI) public

-----------------------------------------------------------
-- SYNTACTIC SEMANTICS
-----------------------------------------------------------

record SyntacticSemantics (E : ℕ → Set) : Set where
  no-eta-equality
  field
    ⟦wk⟧   : Weakening E
    ⟦diag⟧ : {m : ℕ} → Var m =>[ E ] m
    ⟦var⟧  : {n : ℕ} → E n → Infer n

  fresh : {n : ℕ} → E (suc n)
  fresh = lookup ⟦diag⟧ zero

module syntacticSemantics {E : ℕ → Set} (Syn : SyntacticSemantics E) where

  open SyntacticSemantics Syn

  lemma : Semantics E Check Type Infer
  Semantics.⟦wk⟧   lemma = ⟦wk⟧
  Semantics.⟦diag⟧ lemma = ⟦diag⟧
  Semantics.⟦sig⟧  lemma = λ a → `sig a ∘ abs fresh
  Semantics.⟦pi⟧   lemma = λ a → `pi a ∘ abs fresh
  Semantics.⟦nat⟧  lemma = `nat
  Semantics.⟦set⟧  lemma = `set
  Semantics.⟦elt⟧  lemma = `elt
  Semantics.⟦lam⟧  lemma = `lam ∘ abs fresh
  Semantics.⟦per⟧  lemma = `per
  Semantics.⟦zro⟧  lemma = `zro
  Semantics.⟦suc⟧  lemma = `suc
  Semantics.⟦typ⟧  lemma = `typ
  Semantics.⟦emb⟧  lemma = `emb
  Semantics.⟦var⟧  lemma = ⟦var⟧
  Semantics.⟦ann⟧  lemma = `ann
  Semantics.⟦app⟧  lemma = `app
  Semantics.⟦fst⟧  lemma = `fst
  Semantics.⟦snd⟧  lemma = `snd
  Semantics.⟦ind⟧  lemma = `ind ∘ abs fresh

-----------------------------------------------------------
-- EXAMPLES OF SYNTACTIC SEMANTICS
-----------------------------------------------------------

-- Renaming

SyntacticRenaming : SyntacticSemantics Fin
SyntacticSemantics.⟦wk⟧   SyntacticRenaming = lookup
SyntacticSemantics.⟦diag⟧ SyntacticRenaming = pack id
SyntacticSemantics.⟦var⟧  SyntacticRenaming = `var

Renaming : Semantics Fin Check Type Infer
Renaming = syntacticSemantics.lemma SyntacticRenaming

weakI : Weakening Infer
weakI = flip $ Renaming ⊨⟦_⟧I_

weakT : Weakening Type
weakT = flip $ Renaming ⊨⟦_⟧T_

weakC : Weakening Check
weakC = flip $ Renaming ⊨⟦_⟧C_


-- Substitution

SyntacticSubstitution : SyntacticSemantics Infer
SyntacticSemantics.⟦wk⟧   SyntacticSubstitution = weakI
SyntacticSemantics.⟦diag⟧ SyntacticSubstitution = pack `var
SyntacticSemantics.⟦var⟧  SyntacticSubstitution = id

Substitution : Semantics Infer Check Type Infer
Substitution = syntacticSemantics.lemma SyntacticSubstitution

substI : Substituting Infer Infer
substI = Substitution ⊨⟦_⟧I_

substT : Substituting Infer Type
substT = Substitution ⊨⟦_⟧T_

substC : Substituting Infer Check
substC = Substitution ⊨⟦_⟧C_


-- Defining Syntaxes (as per the tt.red definition)

SType : Syntax Type
weak  SType = weakT
subst SType = substT

SInfer : Syntax Infer
weak  SInfer = weakI
subst SInfer = substI

SCheck : Syntax Check
weak  SCheck = weakC
subst SCheck = substC
