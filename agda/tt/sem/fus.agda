module tt.sem.fus where

open import Data.Nat
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_ ; cong ; cong₂)

open import tt.raw
open import tt.env
open import tt.sem

record Fusion
  {E₁ E₂ E₃ MC₁ MC₂ MC₃ MT₁ MT₂ MT₃ MI₁ MI₂ MI₃ : ℕ → Set}
  (S₁     : Semantics E₁ MC₁ MT₁ MI₁)
  (S₂     : Semantics E₂ MC₂ MT₂ MI₂)
  (S₃     : Semantics E₃ MC₃ MT₃ MI₃)
  (E₂₃^R  : Rel E₂ E₃)
  (E^R    : {m n p : ℕ} → Var m =>[ E₁ ] n → Var n =>[ E₂ ] p → Var m =>[ E₃ ] p → Set)
  (MC₂₃^R : Rel MC₂ MC₃)
  (MT₂₃^R : Rel MT₂ MT₃)
  (MI₂₃^R : Rel MI₂ MI₃)
  : Set where

  module S₁ = Semantics S₁
  module S₂ = Semantics S₂
  module S₃ = Semantics S₃

  field
    -- reification back from S₁
    reifyC₁ : MC₁ ⇒ Check
    reifyT₁ : MT₁ ⇒ Type
    reifyI₁ : MI₁ ⇒ Infer

  M^R : (M : ℕ → Set) → Set₁
  M^R M = {m n p : ℕ} (t : M m) (ρ₁ : Var m =>[ E₁ ] n) (ρ₂ : Var n =>[ E₂ ] p) (ρ₃ : Var m =>[ E₃ ] p) → Set

  MC^R : M^R Check
  MC^R t ρ₁ ρ₂ ρ₃ = MC₂₃^R (S₂ ⊨⟦ reifyC₁ (S₁ ⊨⟦ t ⟧C ρ₁) ⟧C ρ₂) (S₃ ⊨⟦ t ⟧C ρ₃)

  MT^R : M^R Type
  MT^R t ρ₁ ρ₂ ρ₃ = MT₂₃^R (S₂ ⊨⟦ reifyT₁ (S₁ ⊨⟦ t ⟧T ρ₁) ⟧T ρ₂) (S₃ ⊨⟦ t ⟧T ρ₃)
  
  MI^R : M^R Infer
  MI^R t ρ₁ ρ₂ ρ₃ = MI₂₃^R (S₂ ⊨⟦ reifyI₁ (S₁ ⊨⟦ t ⟧I ρ₁) ⟧I ρ₂) (S₃ ⊨⟦ t ⟧I ρ₃)

  Kripke^R : {M : ℕ → Set} (MM^R : M^R M) → M^R (M ∘ suc)
  Kripke^R MM^R b ρ₁ ρ₂ ρ₃ =
    {q : ℕ} (inc : _ ⊆ q) {u₂ : E₂ q} {u₃ : E₃ q} → E₂₃^R u₂ u₃ →
    MM^R b (S₁.weakE extend ρ₁ ∙ S₁.fresh) (S₂.weakE inc ρ₂ ∙ u₂) (S₃.weakE inc ρ₃ ∙ u₃)
    
  field
    -- Env
    _⟦∙⟧^R_  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               E^R ρ₁ ρ₂ ρ₃ → {u₂ : E₂ p} {u₃ : E₃ p} → E₂₃^R u₂ u₃ → E^R (S₁.lift ρ₁) (ρ₂ ∙ u₂) (ρ₃ ∙ u₃)
    ⟦wk⟧^R   : {m n p q : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               (inc : p ⊆ q) → E^R ρ₁ ρ₂ ρ₃ → E^R ρ₁ (S₂.weakE inc ρ₂) (S₃.weakE inc ρ₃)
    -- Check
    ⟦sig⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               (A : Type m) → MT^R A ρ₁ ρ₂ ρ₃ →
               (B : Type (suc m)) → Kripke^R MT^R B ρ₁ ρ₂ ρ₃ →
               E^R ρ₁ ρ₂ ρ₃ → MC^R (`sig A B) ρ₁ ρ₂ ρ₃
    ⟦pi⟧^R   : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               (A : Type m) → MT^R A ρ₁ ρ₂ ρ₃ →
               (B : Type (suc m)) → Kripke^R MT^R B ρ₁ ρ₂ ρ₃ →
               E^R ρ₁ ρ₂ ρ₃ → MC^R (`pi A B) ρ₁ ρ₂ ρ₃
    ⟦nat⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               E^R ρ₁ ρ₂ ρ₃ → MC^R `nat ρ₁ ρ₂ ρ₃
    ⟦set⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               (ℓ : ℕ) → E^R ρ₁ ρ₂ ρ₃ → MC^R (`set ℓ) ρ₁ ρ₂ ρ₃
    ⟦lam⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               (b : Check (suc m)) → Kripke^R MC^R b ρ₁ ρ₂ ρ₃ →
               E^R ρ₁ ρ₂ ρ₃ → MC^R (`lam b) ρ₁ ρ₂ ρ₃
    ⟦per⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               (a : Check m) → MC^R a ρ₁ ρ₂ ρ₃ →
               (b : Check m) → MC^R b ρ₁ ρ₂ ρ₃ →
               E^R ρ₁ ρ₂ ρ₃ → MC^R (`per a b) ρ₁ ρ₂ ρ₃
    ⟦zro⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               E^R ρ₁ ρ₂ ρ₃ → MC^R `zro ρ₁ ρ₂ ρ₃
    ⟦suc⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               (m : Check m) → MC^R m ρ₁ ρ₂ ρ₃ → E^R ρ₁ ρ₂ ρ₃ → MC^R (`suc m) ρ₁ ρ₂ ρ₃
    ⟦emb⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
               (e : Infer m) → MI^R e ρ₁ ρ₂ ρ₃ → E^R ρ₁ ρ₂ ρ₃ → MC^R (`emb e) ρ₁ ρ₂ ρ₃
    -- Type
    ⟦El⟧^R   : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p}
               (t : Check m) → MC^R t ρ₁ ρ₂ ρ₃ → E^R ρ₁ ρ₂ ρ₃ → MT^R (El t) ρ₁ ρ₂ ρ₃
    -- Infer
    ⟦var⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p}
               (k : Fin m) (ρ^R : E^R ρ₁ ρ₂ ρ₃) → MI^R (`var k) ρ₁ ρ₂ ρ₃
    ⟦ann⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p}
               (t : Check m) → MC^R t ρ₁ ρ₂ ρ₃ →
               (A : Type m) →  MT^R A ρ₁ ρ₂ ρ₃ → E^R ρ₁ ρ₂ ρ₃ → MI^R (`ann t A) ρ₁ ρ₂ ρ₃ 
    ⟦app⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p}
               (t : Infer m) → MI^R t ρ₁ ρ₂ ρ₃ →
               (u : Check m) → MC^R u ρ₁ ρ₂ ρ₃ → E^R ρ₁ ρ₂ ρ₃ → MI^R (`app t u) ρ₁ ρ₂ ρ₃ 
    ⟦fst⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p}
               (t : Infer m) → MI^R t ρ₁ ρ₂ ρ₃ → E^R ρ₁ ρ₂ ρ₃ → MI^R (`fst t) ρ₁ ρ₂ ρ₃ 
    ⟦snd⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p}
               (t : Infer m) → MI^R t ρ₁ ρ₂ ρ₃ → E^R ρ₁ ρ₂ ρ₃ → MI^R (`snd t) ρ₁ ρ₂ ρ₃ 
    ⟦ind⟧^R  : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p}
               (p : Check m) → MC^R p ρ₁ ρ₂ ρ₃ →
               (z : Check m) → MC^R z ρ₁ ρ₂ ρ₃ →
               (s : Check m) → MC^R s ρ₁ ρ₂ ρ₃ →
               (m : Infer m) → MI^R m ρ₁ ρ₂ ρ₃ → E^R ρ₁ ρ₂ ρ₃ → MI^R (`ind p z s m) ρ₁ ρ₂ ρ₃ 

module fusion
  {E₁ E₂ E₃ MC₁ MC₂ MC₃ MT₁ MT₂ MT₃ MI₁ MI₂ MI₃ : ℕ → Set}
  {S₁     : Semantics E₁ MC₁ MT₁ MI₁}
  {S₂     : Semantics E₂ MC₂ MT₂ MI₂}
  {S₃     : Semantics E₃ MC₃ MT₃ MI₃}
  {E₂₃^R  : Rel E₂ E₃}
  {E^R    : {m n p : ℕ} → Var m =>[ E₁ ] n → Var n =>[ E₂ ] p → Var m =>[ E₃ ] p → Set}
  {MC₂₃^R : Rel MC₂ MC₃}
  {MT₂₃^R : Rel MT₂ MT₃}
  {MI₂₃^R : Rel MI₂ MI₃}
  (φ : Fusion S₁ S₂ S₃ E₂₃^R E^R MC₂₃^R MT₂₃^R MI₂₃^R)
  where

  open Fusion φ

  lemmaTy : {M : ℕ → Set} (MM^R : M^R M) → Set
  lemmaTy {M} MM^R = {m n p : ℕ} (t : M m)
                     {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p}
                     (ρ^R : E^R ρ₁ ρ₂ ρ₃) → MM^R t ρ₁ ρ₂ ρ₃

  abs^R : {M : ℕ → Set} (MM^R : M^R M) (lemmaM : lemmaTy MM^R) → lemmaTy (Kripke^R MM^R)
  abs^R MM^R lemmaM t ρ^R inc u^R = lemmaM t (⟦wk⟧^R inc ρ^R ⟦∙⟧^R u^R)

  -- In the following definition, using `abs^R` prevents Agda from
  -- noticing that the mutual definitions are perfectly structural.

  -- Rather than destroying our nice abstractions, we use a pragma
  -- assuring the typechecker that these definitions are indeed
  -- well-formed.
  
  {-# TERMINATING #-}
  lemmaC : lemmaTy MC^R
  lemmaT : lemmaTy MT^R
  lemmaI : lemmaTy MI^R
  
  lemmaC (`sig A B)  ρ^R = ⟦sig⟧^R A (lemmaT A ρ^R) B (abs^R MT^R lemmaT B ρ^R) ρ^R
  lemmaC (`pi A B)   ρ^R = ⟦pi⟧^R  A (lemmaT A ρ^R) B (abs^R MT^R lemmaT B ρ^R) ρ^R
  lemmaC `nat        ρ^R = ⟦nat⟧^R ρ^R
  lemmaC (`set ℓ)    ρ^R = ⟦set⟧^R ℓ ρ^R
  lemmaC (`lam t)    ρ^R = ⟦lam⟧^R t (abs^R MC^R lemmaC t ρ^R) ρ^R
  lemmaC (`per a b)  ρ^R = ⟦per⟧^R a (lemmaC a ρ^R) b (lemmaC b ρ^R) ρ^R
  lemmaC `zro        ρ^R = ⟦zro⟧^R ρ^R
  lemmaC (`suc m)    ρ^R = ⟦suc⟧^R m (lemmaC m ρ^R) ρ^R
  lemmaC (`emb e)    ρ^R = ⟦emb⟧^R e (lemmaI e ρ^R) ρ^R

  lemmaT (El t) ρ^R = ⟦El⟧^R t (lemmaC t ρ^R) ρ^R
  
  lemmaI (`var k)        ρ^R = ⟦var⟧^R k ρ^R
  lemmaI (`ann t A)      ρ^R = ⟦ann⟧^R t (lemmaC t ρ^R) A (lemmaT A ρ^R) ρ^R
  lemmaI (`app t u)      ρ^R = ⟦app⟧^R t (lemmaI t ρ^R) u (lemmaC u ρ^R) ρ^R
  lemmaI (`fst t)        ρ^R = ⟦fst⟧^R t (lemmaI t ρ^R) ρ^R
  lemmaI (`snd t)        ρ^R = ⟦snd⟧^R t (lemmaI t ρ^R) ρ^R
  lemmaI (`ind p z s m)  ρ^R = ⟦ind⟧^R p (lemmaC p ρ^R) z (lemmaC z ρ^R) s (lemmaC s ρ^R) m (lemmaI m ρ^R) ρ^R

record SyntacticFusion 
  {E₁ E₂ E₃ : ℕ → Set}
  (S₁     : SyntacticSemantics E₁)
  (S₂     : SyntacticSemantics E₂)
  (S₃     : SyntacticSemantics E₃)
  (E₂₃^R  : Rel E₂ E₃)
  (E^R    : {m n p : ℕ} → Var m =>[ E₁ ] n → Var n =>[ E₂ ] p → Var m =>[ E₃ ] p → Set)
  : Set where

  module SS₁ = syntacticSemantics S₁
  module SS₂ = syntacticSemantics S₂
  module SS₃ = syntacticSemantics S₃
  module S₁  = Semantics SS₁.lemma
  module S₂  = Semantics SS₂.lemma
  module S₃  = Semantics SS₃.lemma

  M^R : (M : ℕ → Set) → Set₁
  M^R M = {m n p : ℕ} (t : M m) (ρ₁ : Var m =>[ E₁ ] n) (ρ₂ : Var n =>[ E₂ ] p) (ρ₃ : Var m =>[ E₃ ] p) → Set

  MI^R : M^R Infer
  MI^R t ρ₁ ρ₂ ρ₃ = SS₂.lemma ⊨⟦ SS₁.lemma ⊨⟦ t ⟧I ρ₁ ⟧I ρ₂ ≡ SS₃.lemma ⊨⟦ t ⟧I ρ₃

  field
    -- Env
    _⟦∙⟧^R_   : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
                E^R ρ₁ ρ₂ ρ₃ → {u₂ : E₂ p} {u₃ : E₃ p} → E₂₃^R u₂ u₃ → E^R (S₁.lift ρ₁) (ρ₂ ∙ u₂) (ρ₃ ∙ u₃)
    ⟦wk⟧^R    : {m n p q : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p} →
                (inc : p ⊆ q) → E^R ρ₁ ρ₂ ρ₃ → E^R ρ₁ (S₂.weakE inc ρ₂) (S₃.weakE inc ρ₃)
    -- var
    ⟦var⟧^R   : {m n p : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var n =>[ E₂ ] p} {ρ₃ : Var m =>[ E₃ ] p}
                (k : Fin m) (ρ^R : E^R ρ₁ ρ₂ ρ₃) → MI^R (`var k) ρ₁ ρ₂ ρ₃
    ⟦fresh⟧^R : {m : ℕ} → E₂₃^R {suc m} S₂.fresh S₃.fresh

module syntacticFusion
  {E₁ E₂ E₃ : ℕ → Set}
  {S₁     : SyntacticSemantics E₁}
  {S₂     : SyntacticSemantics E₂}
  {S₃     : SyntacticSemantics E₃}
  {E₂₃^R  : Rel E₂ E₃}
  {E^R    : {m n p : ℕ} → Var m =>[ E₁ ] n → Var n =>[ E₂ ] p → Var m =>[ E₃ ] p → Set}
  (φ : SyntacticFusion S₁ S₂ S₃ E₂₃^R E^R) where

  open SyntacticFusion φ
  open import Data.Product using (_,_ ; uncurry ; proj₁ ; proj₂)

  lemma : Fusion SS₁.lemma SS₂.lemma SS₃.lemma E₂₃^R E^R _≡_ _≡_ _≡_
  lemma = record
    { reifyC₁  = id
    ; reifyT₁  = id
    ; reifyI₁  = id
    ; _⟦∙⟧^R_  = _⟦∙⟧^R_
    ; ⟦wk⟧^R   = ⟦wk⟧^R
    ; ⟦sig⟧^R  = λ _ hA _ hB _ → cong₂ `sig hA (hB extend ⟦fresh⟧^R)
    ; ⟦pi⟧^R   = λ _ hA _ hB _ → cong₂ `pi hA (hB extend ⟦fresh⟧^R)
    ; ⟦nat⟧^R  = λ _ → PEq.refl
    ; ⟦set⟧^R  = λ _ _ → PEq.refl
    ; ⟦lam⟧^R  = λ _ hT _ → cong `lam (hT extend ⟦fresh⟧^R)
    ; ⟦per⟧^R  = λ _ ha _ hb _ → cong₂ `per ha hb
    ; ⟦zro⟧^R  = λ _ → PEq.refl
    ; ⟦suc⟧^R  = λ _ hm _ → cong `suc hm
    ; ⟦emb⟧^R  = λ _ he _ → cong `emb he
    ; ⟦El⟧^R   = λ _ hT _ → cong El hT
    ; ⟦var⟧^R  = ⟦var⟧^R
    ; ⟦ann⟧^R  = λ _ ht _ hA _ → cong₂ `ann ht hA
    ; ⟦app⟧^R  = λ _ ht _ hu _ → cong₂ `app ht hu
    ; ⟦fst⟧^R  = λ _ ht _ → cong `fst ht
    ; ⟦snd⟧^R  = λ _ ht _ → cong `snd ht
    ; ⟦ind⟧^R  = λ _ hp _ hz _ hs _ hm _ →
                 let patt = uncurry $ λ p q r → `ind p q (proj₁ r) (proj₂ r)
                 in cong₂ patt (cong₂ _,_ hp hz) (cong₂ _,_ hs hm)
    }

RenRen : Fusion Renaming Renaming Renaming _≡_ (λ ρ₁ ρ₂ → ∀[ _≡_ ] (trans ρ₁ ρ₂)) _≡_ _≡_ _≡_
RenRen = syntacticFusion.lemma $ record
  { _⟦∙⟧^R_   = λ ρ^R u^R → λ { zero → u^R ; (suc k) → ρ^R k }
  ; ⟦wk⟧^R    = λ inc ρ^R k → cong (lookup inc) (ρ^R k)
  ; ⟦var⟧^R   = λ k ρ^R → cong `var (ρ^R k)
  ; ⟦fresh⟧^R = PEq.refl }

RenSub : Fusion Renaming Substitution Substitution _≡_ (λ ρ₁ ρ₂ → ∀[ _≡_ ] (trans ρ₁ ρ₂)) _≡_ _≡_ _≡_
RenSub = syntacticFusion.lemma $ record
  { _⟦∙⟧^R_   = λ ρ^R u^R → λ { zero → u^R ; (suc k) → ρ^R k }
  ; ⟦wk⟧^R    = λ inc ρ^R k → cong (weakI inc) (ρ^R k)
  ; ⟦var⟧^R   = λ k ρ^R → ρ^R k
  ; ⟦fresh⟧^R = PEq.refl }
  
SubRen : Fusion Substitution Renaming Substitution (_≡_ ∘ `var) (λ ρ₁ ρ₂ → ∀[ _≡_ ] (wk[ weakI ] ρ₂ ρ₁)) _≡_ _≡_ _≡_
SubRen = syntacticFusion.lemma $ record
  { _⟦∙⟧^R_   = λ {_} {_} {_} {ρ₁} ρ^R u^R →
                λ { zero    → u^R
                  ; (suc k) → PEq.trans (Ren^2.lemmaI (lookup ρ₁ k) (λ _ → PEq.refl)) (ρ^R k) }
  ; ⟦wk⟧^R    = λ {_} {_} {_} {_} {ρ₁} inc ρ^R k →
                PEq.trans (PEq.sym (Ren^2.lemmaI (lookup ρ₁ k) (λ _ → PEq.refl)))
                          (cong (weakI inc) (ρ^R k))
  ; ⟦var⟧^R   = λ k ρ^R → ρ^R k
  ; ⟦fresh⟧^R = PEq.refl }

  where module Ren^2 = fusion RenRen

SubSub : Fusion Substitution Substitution Substitution _≡_ (λ ρ₁ ρ₂ → ∀[ _≡_ ] _) _≡_ _≡_ _≡_
SubSub = syntacticFusion.lemma $ record
  { _⟦∙⟧^R_   = λ {_} {_} {_} {ρ₁} ρ^R u^R →
                λ { zero    → u^R
                  ; (suc k) → PEq.trans (fusion.lemmaI RenSub (lookup ρ₁ k) (λ _ → PEq.refl)) (ρ^R k) }
  ; ⟦wk⟧^R    = λ {_} {_} {_} {_} {ρ₁} inc ρ^R k →
                PEq.trans (PEq.sym $ fusion.lemmaI SubRen (lookup ρ₁ k) (λ _ → PEq.refl))
                          (cong (weakI inc) (ρ^R k))
  ; ⟦var⟧^R   = λ k ρ^R → ρ^R k
  ; ⟦fresh⟧^R = PEq.refl }
