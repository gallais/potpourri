module tt.sem.rel where

open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product using (_,_ ; uncurry ; proj₁ ; proj₂)
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_ ; cong ; cong₂)

open import tt.raw
open import tt.env hiding (∀[_])
open import tt.sem

-- Once more it's quite convenient to guide the type inference
-- by using a record to package this definition.

record RelatedRel (Tm E₁ E₂ R₁ R₂ : ℕ → Set) : Set₁ where
  constructor T
  field t : {m n : ℕ} → Tm m → Var m =>[ E₁ ] n → Var m =>[ E₂ ] n → R₁ n → R₂ n → Set

lift : {Tm E₁ E₂ R₁ R₂ : ℕ → Set} → Rel R₁ R₂ → RelatedRel Tm E₁ E₂ R₁ R₂
lift R = T $ λ _ _ _ → R

record Related 
  {E₁ E₂ MC₁ MC₂ MT₁ MT₂ MI₁ MI₂ : ℕ → Set}
  (S₁   : Semantics E₁ MC₁ MT₁ MI₁)
  (S₂   : Semantics E₂ MC₂ MT₂ MI₂)
  (E₁₂^R  : RelatedRel Fin   E₁ E₂ E₁ E₂)
  (MC₁₂^R : RelatedRel Check E₁ E₂ MC₁ MC₂)
  (MT₁₂^R : RelatedRel Type  E₁ E₂ MT₁ MT₂)
  (MI₁₂^R : RelatedRel Infer E₁ E₂ MI₁ MI₂)
  : Set where

  M^R : (M : ℕ → Set) → Set₁
  M^R M = {m n : ℕ} (t : M m) (ρ₁ : Var m =>[ E₁ ] n) (ρ₂ : Var m =>[ E₂ ] n) → Set

  ∀[_] : M^R Fin → {m : ℕ} → Rel (Var m =>[ E₁ ]_) (Var m =>[ E₂ ]_)
  ∀[_] R ρ₁ ρ₂ = (k : Fin _) → R k ρ₁ ρ₂

  E^R : {m : ℕ} → Rel (Var m =>[ E₁ ]_) (Var m =>[ E₂ ]_)
  E^R = ∀[ (λ k ρ₁ ρ₂ → RelatedRel.t E₁₂^R k ρ₁ ρ₂ (lookup ρ₁ k) (lookup ρ₂ k)) ]

  MC^R : M^R Check
  MC^R t ρ₁ ρ₂ = RelatedRel.t MC₁₂^R t ρ₁ ρ₂ (S₁ ⊨⟦ t ⟧C ρ₁) (S₂ ⊨⟦ t ⟧C ρ₂)
  
  MT^R : M^R Type
  MT^R t ρ₁ ρ₂ = RelatedRel.t MT₁₂^R t ρ₁ ρ₂ (S₁ ⊨⟦ t ⟧T ρ₁) (S₂ ⊨⟦ t ⟧T ρ₂)

  MI^R : M^R Infer
  MI^R t ρ₁ ρ₂ = RelatedRel.t MI₁₂^R t ρ₁ ρ₂ (S₁ ⊨⟦ t ⟧I ρ₁) (S₂ ⊨⟦ t ⟧I ρ₂)
  
  module S₁ = Semantics S₁
  module S₂ = Semantics S₂

  Kripke^R : {M : ℕ → Set} (MM^R : M^R M) → M^R (M ∘ suc)
  Kripke^R MM^R b ρ₁ ρ₂ =
    {q : ℕ} (inc : _ ⊆ q) {u₁ : E₁ q} {u₂ : E₂ q} →
    RelatedRel.t E₁₂^R zero (S₁.weakE inc ρ₁ ∙ u₁) (S₂.weakE inc ρ₂ ∙ u₂) u₁ u₂ →
    MM^R b (S₁.weakE inc ρ₁ ∙ u₁) (S₂.weakE inc ρ₂ ∙ u₂)

  field
    -- Env
    ⟦wk⟧^R   : {m n p : ℕ} {k : Fin m} {u₁ : E₁ n} {u₂ : E₂ n} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               (inc : n ⊆ p) → RelatedRel.t E₁₂^R k ρ₁ ρ₂ u₁ u₂ →
               RelatedRel.t E₁₂^R k (S₁.weakE inc ρ₁) (S₂.weakE inc ρ₂) (S₁.⟦wk⟧ inc u₁) (S₂.⟦wk⟧ inc u₂)
    -- Vars
    ⟦varS⟧^R  : {m n : ℕ} {k : Fin m} {u₁ : E₁ n} {u₂ : E₂ n} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
                {v₁ : E₁ n} {v₂ : E₂ n} → RelatedRel.t E₁₂^R k ρ₁ ρ₂ u₁ u₂ →
                RelatedRel.t E₁₂^R (suc k) (ρ₁ ∙ v₁) (ρ₂ ∙ v₂) u₁ u₂
    -- Type
    ⟦sig⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               (A : Type m) → MT^R A ρ₁ ρ₂ →
               (B : Type (suc m)) → Kripke^R MT^R B ρ₁ ρ₂ →
               E^R ρ₁ ρ₂ → MT^R (`sig A B) ρ₁ ρ₂
    ⟦pi⟧^R   : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               (A : Type m) → MT^R A ρ₁ ρ₂ →
               (B : Type (suc m)) → Kripke^R MT^R B ρ₁ ρ₂ →
               E^R ρ₁ ρ₂ → MT^R (`pi A B) ρ₁ ρ₂
    ⟦nat⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               E^R ρ₁ ρ₂ → MT^R `nat ρ₁ ρ₂
    ⟦set⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               (ℓ : ℕ) → E^R ρ₁ ρ₂ → MT^R (`set ℓ) ρ₁ ρ₂
    ⟦elt⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               (e : Infer m) → MI^R e ρ₁ ρ₂ → E^R ρ₁ ρ₂ → MT^R (`elt e) ρ₁ ρ₂
    -- Check
    ⟦lam⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               (b : Check (suc m)) → Kripke^R MC^R b ρ₁ ρ₂ →
               E^R ρ₁ ρ₂ → MC^R (`lam b) ρ₁ ρ₂
    ⟦per⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               (a : Check m) → MC^R a ρ₁ ρ₂ →
               (b : Check m) → MC^R b ρ₁ ρ₂ →
               E^R ρ₁ ρ₂ → MC^R (`per a b) ρ₁ ρ₂
    ⟦zro⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               E^R ρ₁ ρ₂ → MC^R `zro ρ₁ ρ₂
    ⟦suc⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               (m : Check m) → MC^R m ρ₁ ρ₂ → E^R ρ₁ ρ₂ → MC^R (`suc m) ρ₁ ρ₂
    ⟦typ⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               (A : Type m) → MT^R A ρ₁ ρ₂ → E^R ρ₁ ρ₂ → MC^R (`typ A) ρ₁ ρ₂
    ⟦emb⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
               (e : Infer m) → MI^R e ρ₁ ρ₂ → E^R ρ₁ ρ₂ → MC^R (`emb e) ρ₁ ρ₂
    -- Infer
    ⟦var⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n}
               (k : Fin m) (ρ^R : E^R ρ₁ ρ₂) → MI^R (`var k) ρ₁ ρ₂
    ⟦ann⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n}
               (t : Check m) → MC^R t ρ₁ ρ₂ →
               (A : Type m) →  MT^R A ρ₁ ρ₂ → E^R ρ₁ ρ₂ → MI^R (`ann t A) ρ₁ ρ₂ 
    ⟦app⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n}
               (t : Infer m) → MI^R t ρ₁ ρ₂ →
               (u : Check m) → MC^R u ρ₁ ρ₂ → E^R ρ₁ ρ₂ → MI^R (`app t u) ρ₁ ρ₂ 
    ⟦fst⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n}
               (t : Infer m) → MI^R t ρ₁ ρ₂ → E^R ρ₁ ρ₂ → MI^R (`fst t) ρ₁ ρ₂ 
    ⟦snd⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n}
               (t : Infer m) → MI^R t ρ₁ ρ₂ → E^R ρ₁ ρ₂ → MI^R (`snd t) ρ₁ ρ₂ 
    ⟦ind⟧^R  : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n}
               (p : Check m) → MC^R p ρ₁ ρ₂ →
               (z : Check m) → MC^R z ρ₁ ρ₂ →
               (s : Check m) → MC^R s ρ₁ ρ₂ →
               (m : Infer m) → MI^R m ρ₁ ρ₂ → E^R ρ₁ ρ₂ → MI^R (`ind p z s m) ρ₁ ρ₂ 

module related
  {E₁ E₂ MC₁ MC₂ MT₁ MT₂ MI₁ MI₂ : ℕ → Set}
  {S₁     : Semantics E₁ MC₁ MT₁ MI₁}
  {S₂     : Semantics E₂ MC₂ MT₂ MI₂}
  {E₁₂^R  : RelatedRel Fin   E₁ E₂ E₁ E₂}
  {MC₁₂^R : RelatedRel Check E₁ E₂ MC₁ MC₂}
  {MT₁₂^R : RelatedRel Type  E₁ E₂ MT₁ MT₂}
  {MI₁₂^R : RelatedRel Infer E₁ E₂ MI₁ MI₂}
  (Rel    : Related S₁ S₂ E₁₂^R MC₁₂^R MT₁₂^R MI₁₂^R)
  where

  open Related Rel

  lemmaTy : {M : ℕ → Set} (MM^R : M^R M) → Set
  lemmaTy {M} MM^R = {m n : ℕ} (t : M m) {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
                     E^R ρ₁ ρ₂ → MM^R t ρ₁ ρ₂

  abs^R : {M : ℕ → Set} (MM^R : M^R M) (lemmaM : lemmaTy MM^R) → lemmaTy (Kripke^R MM^R)
  abs^R MM^R lemmaM t ρ^R inc u^R = lemmaM t $ λ { zero → u^R ; (suc k) → ⟦varS⟧^R (⟦wk⟧^R inc (ρ^R k)) }

  -- In the following definition, using `abs^R` prevents Agda from
  -- noticing that the mutual definitions are perfectly structural.

  -- Rather than destroying our nice abstractions, we use a pragma
  -- assuring the typechecker that these definitions are indeed
  -- well-formed.
  
  {-# TERMINATING #-}
  lemmaC : lemmaTy MC^R
  lemmaT : lemmaTy MT^R
  lemmaI : lemmaTy MI^R
  
  lemmaC (`lam b)    ρ^R = ⟦lam⟧^R b (abs^R MC^R lemmaC b ρ^R) ρ^R
  lemmaC (`per a b)  ρ^R = ⟦per⟧^R a (lemmaC a ρ^R) b (lemmaC b ρ^R) ρ^R
  lemmaC `zro        ρ^R = ⟦zro⟧^R ρ^R
  lemmaC (`suc m)    ρ^R = ⟦suc⟧^R m (lemmaC m ρ^R) ρ^R
  lemmaC (`typ A)    ρ^R = ⟦typ⟧^R A (lemmaT A ρ^R) ρ^R
  lemmaC (`emb e)    ρ^R = ⟦emb⟧^R e (lemmaI e ρ^R) ρ^R
  
  lemmaT (`sig A B)  ρ^R = ⟦sig⟧^R A (lemmaT A ρ^R) B (abs^R MT^R lemmaT B ρ^R) ρ^R
  lemmaT (`pi A B)   ρ^R = ⟦pi⟧^R  A (lemmaT A ρ^R) B (abs^R MT^R lemmaT B ρ^R) ρ^R
  lemmaT `nat        ρ^R = ⟦nat⟧^R ρ^R
  lemmaT (`set ℓ)    ρ^R = ⟦set⟧^R ℓ ρ^R
  lemmaT (`elt e)    ρ^R = ⟦elt⟧^R e (lemmaI e ρ^R) ρ^R
  
  lemmaI (`var k)       ρ^R = ⟦var⟧^R k ρ^R
  lemmaI (`ann t A)     ρ^R = ⟦ann⟧^R t (lemmaC t ρ^R) A (lemmaT A ρ^R) ρ^R
  lemmaI (`app t u)     ρ^R = ⟦app⟧^R t (lemmaI t ρ^R) u (lemmaC u ρ^R) ρ^R
  lemmaI (`fst t)       ρ^R = ⟦fst⟧^R t (lemmaI t ρ^R) ρ^R
  lemmaI (`snd t)       ρ^R = ⟦snd⟧^R t (lemmaI t ρ^R) ρ^R
  lemmaI (`ind p z s m) ρ^R = ⟦ind⟧^R p (lemmaC p ρ^R) z (lemmaC z ρ^R) s (lemmaC s ρ^R) m (lemmaI m ρ^R) ρ^R

record SyntacticRelated 
  {E₁ E₂ : ℕ → Set}
  (S₁   : SyntacticSemantics E₁)
  (S₂   : SyntacticSemantics E₂)
  (E₁₂^R  : RelatedRel Fin E₁ E₂ E₁ E₂)
  : Set where

  module SS₁ = syntacticSemantics S₁
  module SS₂ = syntacticSemantics S₂
  module S₁  = Semantics SS₁.lemma
  module S₂  = Semantics SS₂.lemma

  M^R : (M : ℕ → Set) → Set₁
  M^R M = {m n : ℕ} (t : M m) (ρ₁ : Var m =>[ E₁ ] n) (ρ₂ : Var m =>[ E₂ ] n) → Set

  ∀[_] : M^R Fin → {m : ℕ} → Rel (Var m =>[ E₁ ]_) (Var m =>[ E₂ ]_)
  ∀[_] R ρ₁ ρ₂ = (k : Fin _) → R k ρ₁ ρ₂

  E^R : {m : ℕ} → Rel (Var m =>[ E₁ ]_) (Var m =>[ E₂ ]_)
  E^R = ∀[ (λ k ρ₁ ρ₂ → RelatedRel.t E₁₂^R k ρ₁ ρ₂ (lookup ρ₁ k) (lookup ρ₂ k)) ]

  MI^R : M^R Infer
  MI^R t ρ₁ ρ₂ = SS₁.lemma ⊨⟦ t ⟧I ρ₁ ≡ SS₂.lemma ⊨⟦ t ⟧I ρ₂

  field
    -- Env
    ⟦wk⟧^R    : {m n p : ℕ} {k : Fin m} {u₁ : E₁ n} {u₂ : E₂ n} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
                (inc : n ⊆ p) → RelatedRel.t E₁₂^R k ρ₁ ρ₂ u₁ u₂ →
                RelatedRel.t E₁₂^R k (S₁.weakE inc ρ₁) (S₂.weakE inc ρ₂) (S₁.⟦wk⟧ inc u₁) (S₂.⟦wk⟧ inc u₂)
    ⟦varS⟧^R  : {m n : ℕ} {k : Fin m} {u₁ : E₁ n} {u₂ : E₂ n} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} →
                {v₁ : E₁ n} {v₂ : E₂ n} → RelatedRel.t E₁₂^R k ρ₁ ρ₂ u₁ u₂ →
                RelatedRel.t E₁₂^R (suc k) (ρ₁ ∙ v₁) (ρ₂ ∙ v₂) u₁ u₂
    -- var
    ⟦var⟧^R   : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n}
                (k : Fin m) (ρ^R : E^R ρ₁ ρ₂) → MI^R (`var k) ρ₁ ρ₂
    ⟦fresh⟧^R : {m n : ℕ} {ρ₁ : Var m =>[ E₁ ] n} {ρ₂ : Var m =>[ E₂ ] n} → E^R ρ₁ ρ₂ →
                let ρ₁′ = S₁.weakE extend ρ₁
                    ρ₂′ = S₂.weakE extend ρ₂
                in RelatedRel.t E₁₂^R zero (ρ₁′ ∙ S₁.fresh) (ρ₂′ ∙ S₂.fresh) S₁.fresh S₂.fresh


module syntacticRelated
  {E₁ E₂ : ℕ → Set}
  {S₁     : SyntacticSemantics E₁}
  {S₂     : SyntacticSemantics E₂}
  {E₁₂^R  : RelatedRel Fin E₁ E₂ E₁ E₂}
  (Rel    : SyntacticRelated S₁ S₂ E₁₂^R)
  where

  open SyntacticRelated Rel

  lemma : Related SS₁.lemma SS₂.lemma E₁₂^R (lift _≡_) (lift _≡_) (lift _≡_)
  lemma = record
    { ⟦wk⟧^R   = ⟦wk⟧^R
    ; ⟦varS⟧^R = ⟦varS⟧^R
    ; ⟦sig⟧^R  = λ _ hA _ hB ρ^R → cong₂ `sig hA (hB extend (⟦fresh⟧^R ρ^R))
    ; ⟦pi⟧^R   = λ _ hA _ hB ρ^R → cong₂ `pi  hA (hB extend (⟦fresh⟧^R ρ^R))
    ; ⟦nat⟧^R  = λ _ → PEq.refl
    ; ⟦set⟧^R  = λ _ _ → PEq.refl
    ; ⟦elt⟧^R  = λ _ hE _ → cong `elt hE
    ; ⟦lam⟧^R  = λ _ hb ρ^R → cong `lam (hb extend (⟦fresh⟧^R ρ^R))
    ; ⟦per⟧^R  = λ _ ha _ hb _ → cong₂ `per ha hb
    ; ⟦zro⟧^R  = λ _ → PEq.refl
    ; ⟦suc⟧^R  = λ _ hm _ → cong `suc hm
    ; ⟦typ⟧^R  = λ _ hA _ → cong `typ hA
    ; ⟦emb⟧^R  = λ _ he _ → cong `emb he
    ; ⟦var⟧^R  = ⟦var⟧^R
    ; ⟦ann⟧^R  = λ _ ht _ hA _ → cong₂ `ann ht hA
    ; ⟦app⟧^R  = λ _ ht _ hu _ → cong₂ `app ht hu
    ; ⟦fst⟧^R  = λ _ ht _ → cong `fst ht
    ; ⟦snd⟧^R  = λ _ ht _ → cong `snd ht
    ; ⟦ind⟧^R  = λ _ hp _ hz _ hs _ hm _ →
                  let patt = uncurry $ λ p q r → `ind p q (proj₁ r) (proj₂ r)
                  in cong₂ patt (cong₂ _,_ hp hz) (cong₂ _,_ hs hm)
    }

RenSubVar : Related Renaming Substitution (lift $ _≡_ ∘ `var) _ _ _
RenSubVar = syntacticRelated.lemma $ record
  { ⟦wk⟧^R    = λ inc eq → cong (weakI inc) eq
  ; ⟦varS⟧^R  = id
  ; ⟦var⟧^R   = λ k ρ^R → ρ^R k
  ; ⟦fresh⟧^R = λ _ → PEq.refl }

SynExt : {E : ℕ → Set} (Syn : SyntacticSemantics E) →
         let S = syntacticSemantics.lemma Syn in Related S S (lift _≡_) _ _ _
SynExt Syn = syntacticRelated.lemma $ record
  { ⟦wk⟧^R    = λ inc → cong (⟦wk⟧ inc)
  ; ⟦varS⟧^R  = id
  ; ⟦var⟧^R   = λ k ρ^R → cong ⟦var⟧ (ρ^R k)
  ; ⟦fresh⟧^R = λ _ → PEq.refl }
  where open SyntacticSemantics Syn

RenExt : Related Renaming Renaming (lift _≡_) _ _ _
RenExt = SynExt SyntacticRenaming

SubExt : Related Substitution Substitution (lift _≡_) _ _ _
SubExt = SynExt SyntacticSubstitution
