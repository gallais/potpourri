
\begin{code}
module fusion where

open import Level
open import Data.Unit
open import Data.Product
open import Function
open import models
open import properties
open import Relation.Binary.On
open import Relation.Binary.PropositionalEquality as PEq renaming (refl to trivial) using (_≡_ ; cong ; cong₂)

record Fusable
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REBC ℓ^RM : Level}
  {EnvA   : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB   : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC   : (Γ : Con) (σ : ty) → Set ℓ^EC}
  {ModA   : (Γ : Con) (σ : ty) → Set ℓ^MA}
  {ModB   : (Γ : Con) (σ : ty) → Set ℓ^MB}
  {ModC   : (Γ : Con) (σ : ty) → Set ℓ^MC}
  (semA   : Semantics EnvA ModA)
  (semB   : Semantics EnvB ModB)
  (semC   : Semantics EnvC ModC)
  (RelEnvBC : {Γ : Con} {σ : ty} (eB : EnvB Γ σ) (eC : EnvC Γ σ) → Set ℓ^REBC)
  (RelEnv   : {Θ Δ Γ : Con} (eA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (eC : Θ [ EnvC ] Γ) → Set ℓ^RE)
  (RelMod   : {Γ : Con} {σ : ty} (mB : ModB Γ σ) (mC : ModC Γ σ) → Set ℓ^RM)
  : Set (ℓ^RM ⊔ ℓ^RE ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA ⊔ ℓ^MA ⊔ ℓ^REBC)
  where
  module SemA = Semantics semA
  module SemB = Semantics semB
  module SemC = Semantics semC
  field
    reifyA  : {Γ : Con} {σ : ty} (m : ModA Γ σ) → Γ ⊢ σ
    RelEnv∙ : ({Γ Δ Θ : Con} {σ : ty} {ρA : Δ [ EnvA ] Γ} {ρB : Θ [ EnvB ] Δ} {ρC : Θ [ EnvC ] Γ}
               {uB : EnvB Θ σ} {uC : EnvC Θ σ} (ρR : RelEnv ρA ρB ρC) (uR : RelEnvBC uB uC) →
               RelEnv ([ EnvA ] wk[ SemA.wk ] (step refl) ρA `∙ SemA.embed σ here!)
                      ([ EnvB ] ρB `∙ uB)
                      ([ EnvC ] ρC `∙ uC))
    RelEnvWk : {Γ Δ Θ E : Con} (inc : Θ ⊆ E)
               {ρA : Δ [ EnvA ] Γ} {ρB : Θ [ EnvB ] Δ} {ρC : Θ [ EnvC ] Γ} (ρR : RelEnv ρA ρB ρC) →
               RelEnv ρA (wk[ SemB.wk ] inc ρB) (wk[ SemC.wk ] inc ρC)
    R⟦var⟧  : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ)
              (ρR : RelEnv ρA ρB ρC) →
              RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `var v ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `var v ⟧ ρC)
    R⟦$⟧    : {Γ Δ Θ : Con} {σ τ : ty} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ)
            (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : RelEnv ρA ρB ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ f ⟧ ρA) ⟧ ρB) (semC ⊨⟦ f ⟧ ρC) → 
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ t ⟧ ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ f `$ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ f `$ t ⟧ ρC)
    R⟦λ⟧    : {Γ Δ Θ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ)
              (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) (ρR : RelEnv ρA ρB ρC) →
             (r : {E : Con} (inc : Θ ⊆ E) {uB : EnvB E σ} {uC : EnvC E σ} (uR : RelEnvBC uB uC) →
                  RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ t ⟧ ([ EnvA ] wk[ SemA.wk ] (step refl) ρA `∙ SemA.embed σ here!)) ⟧
                              ([ EnvB ] wk[ SemB.wk ] inc ρB `∙ uB))
                        (semC ⊨⟦ t ⟧ ([ EnvC ] wk[ SemC.wk ] inc ρC `∙ uC))) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `λ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `λ t ⟧ ρC)
    R⟦⟨⟩⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : RelEnv ρA ρB ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `⟨⟩ ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `⟨⟩ ⟧ ρC)
    R⟦tt⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : RelEnv ρA ρB ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `tt ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `tt ⟧ ρC)
    R⟦ff⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : RelEnv ρA ρB ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `ff ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `ff ⟧ ρC)
    R⟦ifte⟧ : {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
            (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : RelEnv ρA ρB ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ b ⟧ ρA) ⟧ ρB) (semC ⊨⟦ b ⟧ ρC) → 
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ l ⟧ ρA) ⟧ ρB) (semC ⊨⟦ l ⟧ ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ r ⟧ ρA) ⟧ ρB) (semC ⊨⟦ r ⟧ ρC) →
            RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ `ifte b l r ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `ifte b l r ⟧ ρC)

module Fusion
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REB ℓ^RM : Level}
  {EnvA   : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB   : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC   : (Γ : Con) (σ : ty) → Set ℓ^EC}
  {ModA   : (Γ : Con) (σ : ty) → Set ℓ^MA}
  {ModB   : (Γ : Con) (σ : ty) → Set ℓ^MB}
  {ModC   : (Γ : Con) (σ : ty) → Set ℓ^MC}
  {semA   : Semantics EnvA ModA}
  {semB   : Semantics EnvB ModB}
  {semC   : Semantics EnvC ModC}
  {RelEnvBC : {Γ : Con} {σ : ty} (eB : EnvB Γ σ) (eC : EnvC Γ σ) → Set ℓ^REB}
  {RelEnv : {Θ Δ Γ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) → Set ℓ^RE}
  {RelMod : {Γ : Con} {σ : ty} (mB : ModB Γ σ) (mC : ModC Γ σ) → Set ℓ^RM}
  (fusable : Fusable semA semB semC RelEnvBC RelEnv RelMod)
  where
  open Fusable fusable
  
  fusion :
    {Γ Δ Θ : Con} {σ : ty}
    (t : Γ ⊢ σ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ)
             (ρR : RelEnv ρA ρB ρC) →
    RelMod (semB ⊨⟦ reifyA (semA ⊨⟦ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ t ⟧ ρC)
  fusion (`var v)      ρA ρB ρC ρR = R⟦var⟧ v ρA ρB ρC ρR
  fusion (f `$ t)      ρA ρB ρC ρR = R⟦$⟧ f t ρA ρB ρC ρR (fusion f ρA ρB ρC ρR) (fusion t ρA ρB ρC ρR)
  fusion (`λ t)        ρA ρB ρC ρR = R⟦λ⟧ t ρA ρB ρC ρR $ λ inc uR →
                                     fusion t _ _ _ (RelEnv∙ (RelEnvWk inc ρR) uR)
  fusion `⟨⟩           ρA ρB ρC ρR = R⟦⟨⟩⟧ ρA ρB ρC ρR
  fusion `tt           ρA ρB ρC ρR = R⟦tt⟧ ρA ρB ρC ρR
  fusion `ff           ρA ρB ρC ρR = R⟦ff⟧ ρA ρB ρC ρR
  fusion (`ifte b l r) ρA ρB ρC ρR = R⟦ifte⟧ b l r ρA ρB ρC ρR ihb ihl ihr
    where ihb = fusion b ρA ρB ρC ρR
          ihl = fusion l ρA ρB ρC ρR
          ihr = fusion r ρA ρB ρC ρR

record SyntacticFusable
  {ℓ^EA ℓ^EB ℓ^EC ℓ^REBC ℓ^RE : Level}
  {EnvA  : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB  : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC  : (Γ : Con) (σ : ty) → Set ℓ^EC}
  (synA : Syntactic EnvA) (synB : Syntactic EnvB) (synC : Syntactic EnvC)
  (RelEnvBC : {Γ : Con} {σ : ty} (eB : EnvB Γ σ) (eC : EnvC Γ σ) → Set ℓ^REBC)
  (RelEnv : {Θ Δ Γ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) → Set ℓ^RE)
  : Set (ℓ^RE ⊔ ℓ^REBC ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA)
  where
  module SynA = Syntactic synA
  module SynB = Syntactic synB
  module SynC = Syntactic synC
  field
    RelEnv∙ : ({Γ Δ Θ : Con} {σ : ty} {ρA : Δ [ EnvA ] Γ} {ρB : Θ [ EnvB ] Δ} {ρC : Θ [ EnvC ] Γ}
               {uB : EnvB Θ σ} {uC : EnvC Θ σ} (ρR : RelEnv ρA ρB ρC) (uR : RelEnvBC uB uC) →
               RelEnv ([ EnvA ] wk[ SynA.wk ] (step refl) ρA `∙ SynA.embed σ here!)
                      ([ EnvB ] ρB `∙ uB)
                      ([ EnvC ] ρC `∙ uC))
    RelEnvWk : {Γ Δ Θ E : Con} (inc : Θ ⊆ E)
               {ρA : Δ [ EnvA ] Γ} {ρB : Θ [ EnvB ] Δ} {ρC : Θ [ EnvC ] Γ} (ρR : RelEnv ρA ρB ρC) →
               RelEnv ρA (wk[ SynB.wk ] inc ρB) (wk[ SynC.wk ] inc ρC)
    R⟦var⟧  : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ)
              (ρR : RelEnv ρA ρB ρC) →
              syntactic synB ⊨⟦ syntactic synA ⊨⟦ `var v ⟧ ρA ⟧ ρB ≡ syntactic synC ⊨⟦ `var v ⟧ ρC
    embedBC : {Γ : Con} {σ : ty} → RelEnvBC {Γ ∙ σ} (SynB.embed σ here!) (SynC.embed σ here!)


syntacticFusable : 
  {ℓ^EA ℓ^EB ℓ^EC ℓ^RE ℓ^REBC : Level}
  {EnvA  : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB  : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC  : (Γ : Con) (σ : ty) → Set ℓ^EC}
  {synA : Syntactic EnvA} {synB : Syntactic EnvB} {synC : Syntactic EnvC}
  {RelEnvBC : {Γ : Con} {σ : ty} (eB : EnvB Γ σ) (eC : EnvC Γ σ) → Set ℓ^REBC}
  {RelEnv : {Θ Δ Γ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) → Set ℓ^RE}
  (synF : SyntacticFusable synA synB synC RelEnvBC RelEnv) →
   let open SyntacticFusable synF
   in Fusable (syntactic synA) (syntactic synB) (syntactic synC) RelEnvBC RelEnv _≡_
syntacticFusable synF =
  let open SyntacticFusable synF in
  record
    { reifyA    = id
    ; RelEnv∙   = RelEnv∙
    ; RelEnvWk  = RelEnvWk
    ; R⟦var⟧    = R⟦var⟧
    ; R⟦$⟧      = λ f t ρA ρB ρC ρR → cong₂ _`$_
    ; R⟦λ⟧      = λ t ρA ρB ρC ρR r → cong `λ (r (step refl) embedBC)
    ; R⟦⟨⟩⟧     = λ ρA ρB ρC ρR → trivial
    ; R⟦tt⟧     = λ ρA ρB ρC ρR → trivial
    ; R⟦ff⟧     = λ ρA ρB ρC ρR → trivial
    ; R⟦ifte⟧   = λ b l r ρA ρB ρC ρR eqb eql → cong₂ (uncurry `ifte) (cong₂ _,_ eqb eql)
    }



syntacticRenaming : Syntactic (flip _∈_)
syntacticRenaming = record { wk = wk^∈ ; embed = λ _ → id ; ⟦var⟧ = `var }

syntacticSubstitution : Syntactic _⊢_
syntacticSubstitution = record { wk = wk^⊢ ; embed = λ _ → `var ; ⟦var⟧ = id }

`var-inj : {Γ : Con} {σ : ty} {pr₁ pr₂ : σ ∈ Γ} (eq : (Γ ⊢ σ ∋ `var pr₁) ≡ `var pr₂) → pr₁ ≡ pr₂
`var-inj trivial = trivial

RenamingFusable :
  SyntacticFusable syntacticRenaming syntacticRenaming syntacticRenaming
                   _≡_ (λ ρA ρB ρC → (σ : ty) (pr : σ ∈ _) → ρB σ (ρA σ pr) ≡ ρC σ pr)
RenamingFusable =
  record { RelEnv∙   = λ ρR eq → [ eq , ρR ]
         ; RelEnvWk  = λ inc ρR σ pr → cong (inc σ) (ρR σ pr)
         ; R⟦var⟧    = λ v _ _ _ ρR → cong `var (ρR _ v)
         ; embedBC   = trivial }

RenamingSubstitutionFusable :
  SyntacticFusable syntacticRenaming syntacticSubstitution syntacticSubstitution
                   _≡_ (λ ρA ρB ρC → (σ : ty) (pr : σ ∈ _) → ρB σ (ρA σ pr) ≡ ρC σ pr)
RenamingSubstitutionFusable =
  record { RelEnv∙   = λ ρR eq → [ eq , ρR ]
         ; RelEnvWk  = λ inc ρR σ pr → cong (Renaming ⊨⟦_⟧ inc) (ρR σ pr)
         ; R⟦var⟧    = λ v _ _ _ ρR → ρR _ v
         ; embedBC   = trivial }

SubstitutionRenamingFusable :
  SyntacticFusable syntacticSubstitution syntacticRenaming syntacticSubstitution
                   (λ v t → `var v ≡ t) (λ ρA ρB ρC → (σ : ty) (pr : σ ∈ _) → Renaming ⊨⟦ ρA σ pr ⟧ ρB ≡ ρC σ pr)
SubstitutionRenamingFusable =
  let module RenRen = Fusion (syntacticFusable RenamingFusable) in
  record { RelEnv∙   = λ {_} {_} {_} {_} {ρA} {ρB} {ρC} ρR eq → [ eq , (λ σ pr →
                         PEq.trans (RenRen.fusion (ρA σ pr) (step refl) _ ρB (λ _ _ → trivial))
                                   (ρR σ pr)) ]
         ; RelEnvWk  = λ inc {ρA} {ρB} {ρC} ρR σ pr →
                         PEq.trans (PEq.sym (RenRen.fusion (ρA σ pr) ρB _ _ (λ _ _ → trivial)))
                                   (cong (Renaming ⊨⟦_⟧ inc) (ρR σ pr))
         ; R⟦var⟧    = λ v _ _ _ ρR → ρR _ v
         ; embedBC   = trivial }

SubstitutionFusable :
  SyntacticFusable syntacticSubstitution syntacticSubstitution syntacticSubstitution
                   _≡_ (λ ρA ρB ρC → (σ : ty) (pr : σ ∈ _) → Substitution ⊨⟦ ρA σ pr ⟧ ρB ≡ ρC σ pr)
SubstitutionFusable =
  let module RenSubst = Fusion (syntacticFusable RenamingSubstitutionFusable)
      module SubstRen = Fusion (syntacticFusable SubstitutionRenamingFusable) in
  record { RelEnv∙   = λ {_} {_} {_} {_} {ρA} {ρB} {ρC} ρR eq → [ eq , (λ σ pr →
                         PEq.trans (RenSubst.fusion (ρA σ pr) (step refl) _ ρB (λ _ _ → trivial))
                                   (ρR σ pr)) ]
         ; RelEnvWk  = λ inc {ρA} {ρB} {ρC} ρR σ pr →
                         PEq.trans (PEq.sym (SubstRen.fusion (ρA σ pr) ρB _ _ (λ _ _ → trivial)))
                                   (cong (Renaming ⊨⟦_⟧ inc) (ρR σ pr))
         ; R⟦var⟧    = λ v _ _ _ ρR → ρR _ v
         ; embedBC   = trivial } 

ifteRenNorm :
      {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      (ρA : Δ [ flip _∈_ ] Γ) (ρB : Θ [ _⊨^βιξη_ ] Δ)
      (ρC : Θ [ _⊨^βιξη_ ] Γ) →
      (ρR : (σ : ty) (pr : σ ∈ Γ) → EQREL Θ σ (ρB σ (ρA σ pr)) (ρC σ pr)) →
      Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ b ⟧ ρA) ⟧ ρB ≡
      Normalise^βιξη ⊨⟦ b ⟧ ρC →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ l ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ l ⟧ ρC) →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ r ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ r ⟧ ρC) →
      EQREL Θ σ
      (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ `ifte b l r ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρC)
ifteRenNorm b l r ρA ρB ρC ρR eqb eql eqr
  with Normalise^βιξη ⊨⟦ Renaming ⊨⟦ b ⟧ ρA ⟧ ρB
     | Normalise^βιξη ⊨⟦ b ⟧ ρC
ifteRenNorm b l r ρA ρB ρC ρR trivial eql eqr | `embed t | `embed .t =
  reflect^EQREL _ (cong₂ (uncurry `ifte) (cong₂ _,_ trivial (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `embed t | `tt
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `embed t | `ff
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `tt | `embed t
ifteRenNorm b l r ρA ρB ρC ρR trivial eql eqr | `tt | `tt = eql
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `tt | `ff
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `ff | `embed t
ifteRenNorm b l r ρA ρB ρC ρR () eql eqr | `ff | `tt
ifteRenNorm b l r ρA ρB ρC ρR trivial eql eqr | `ff | `ff = eqr

RenamingNormaliseFusable :
  Fusable Renaming Normalise^βιξη Normalise^βιξη
          (EQREL _ _) (λ ρA ρB ρC → (σ : ty) (pr : σ ∈ _) → EQREL _ σ (ρB σ (ρA σ pr)) (ρC σ pr))
          (EQREL _ _)
RenamingNormaliseFusable =
  record
    { reifyA   = id
    ; RelEnv∙  = λ ρR uR → [ uR , ρR ]
    ; RelEnvWk = λ inc ρR → λ σ pr → wk^EQREL σ inc (ρR σ pr)
    ; R⟦var⟧   = λ v _ _ _ ρR → ρR _ v
    ; R⟦$⟧     = λ _ _ _ _ _ _ r → r refl
    ; R⟦λ⟧     = λ _ _ _ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ _ _ _ → tt
    ; R⟦tt⟧    = λ _ _ _ _ → trivial
    ; R⟦ff⟧    = λ _ _ _ _ → trivial
    ; R⟦ifte⟧  = ifteRenNorm
    }


ifteSubstNorm :
     {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      (ρA : Δ [ _⊢_ ] Γ) (ρB : Θ [ _⊨^βιξη_ ] Δ)
      (ρC : Θ [ _⊨^βιξη_ ] Γ) →
      ((σ₁ : ty) (pr : σ₁ ∈ Δ) → EQREL Θ σ₁ (ρB σ₁ pr) (ρB σ₁ pr)) ×
      ((σ₁ : ty) (pr : σ₁ ∈ Γ) {Θ₁ : Con} (inc : Θ ⊆ Θ₁) →
       EQREL Θ₁ σ₁
       (Normalise^βιξη ⊨⟦ ρA σ₁ pr ⟧
        (λ σ₂ pr₁ → wk^βιξη σ₂ inc $ ρB σ₂ pr₁))
       (wk^βιξη σ₁ inc $ ρC σ₁ pr))
      ×
      ((σ₁ : ty) (pr : σ₁ ∈ Γ) →
       EQREL Θ σ₁ (Normalise^βιξη ⊨⟦ ρA σ₁ pr ⟧ ρB) (ρC σ₁ pr)) →
      Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ b ⟧ ρA) ⟧ ρB ≡
      Normalise^βιξη ⊨⟦ b ⟧ ρC →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ l ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ l ⟧ ρC) →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ r ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ r ⟧ ρC) →
      EQREL Θ σ
      (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ `ifte b l r ⟧ ρA) ⟧ ρB)
      (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρC)
ifteSubstNorm b l r ρA ρB ρC ρR eqb eql eqr
  with Normalise^βιξη ⊨⟦ Substitution ⊨⟦ b ⟧ ρA ⟧ ρB
     | Normalise^βιξη ⊨⟦ b ⟧ ρC
ifteSubstNorm b l r ρA ρB ρC ρR trivial eql eqr | `embed t | `embed .t =
  reflect^EQREL _ (cong₂ (uncurry `ifte) (cong₂ _,_ trivial (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `embed t | `tt
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `embed t | `ff
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `tt | `embed t
ifteSubstNorm b l r ρA ρB ρC ρR trivial eql eqr | `tt | `tt = eql
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `tt | `ff
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `ff | `embed t
ifteSubstNorm b l r ρA ρB ρC ρR () eql eqr | `ff | `tt
ifteSubstNorm b l r ρA ρB ρC ρR trivial eql eqr | `ff | `ff = eqr

wk-refl : {Γ : Con} (σ : ty) {T U : Γ ⊨^βιξη σ} →
          EQREL Γ σ T U → EQREL Γ σ (wk^βιξη σ refl T) U
wk-refl `Unit     eq = tt
wk-refl `Bool     eq = {!!}
wk-refl (σ `→ τ)  eq = eq

wk^2 : {Θ Δ Γ : Con} (σ : ty) (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ) {T U : Γ ⊨^βιξη σ} →
       EQREL Γ σ T U → EQREL Θ σ (wk^βιξη σ inc₂ $ wk^βιξη σ inc₁ T) (wk^βιξη σ (trans inc₁ inc₂) U)
wk^2 `Unit     inc₁ inc₂ eq = tt
wk^2 `Bool     inc₁ inc₂ eq = {!!}
wk^2 (σ `→ τ)  inc₁ inc₂ eq = λ inc₃ → eq (trans inc₁ $ trans inc₂ inc₃)
 

SubstitutionNormaliseFusable :
  Fusable Substitution Normalise^βιξη Normalise^βιξη
          (EQREL _ _)
          (λ ρA ρB ρC → ((σ : ty) (pr : σ ∈ _) → EQREL _ σ (ρB σ pr) (ρB σ pr))
                      × ((σ : ty) (pr : σ ∈ _) {Θ : Con} (inc : _ ⊆ Θ) →
                         EQREL Θ σ (Normalise^βιξη ⊨⟦ ρA σ pr ⟧ (λ σ pr → wk^βιξη σ inc $ ρB σ pr))
                                   (wk^βιξη σ inc $ ρC σ pr))
                      × ((σ : ty) (pr : σ ∈ _) → EQREL _ σ (Normalise^βιξη ⊨⟦ ρA σ pr ⟧ ρB) (ρC σ pr)))
          (EQREL _ _)
SubstitutionNormaliseFusable =
  let module RenNorm = Fusion RenamingNormaliseFusable
      module EqNorm  = Related RelatableNormalise in
  record
    { reifyA   = id
    ; RelEnv∙  = λ {_} {_} {_} {_} {ρA} {ρB} {ρC} ρR uR →
                     [ reflEQREL _ uR , proj₁ ρR ] 
                   , [ (λ {Θ} inc → wk^EQREL _ inc uR)
                     , (λ σ pr {Θ} inc →
                       transEQREL σ (RenNorm.fusion (ρA σ pr) (step refl) _ _
                                                    (λ σ pr → wk^EQREL σ inc (proj₁ ρR σ pr)))
                                    ((proj₁ ∘ proj₂) ρR σ pr inc)) ]
                     , [ uR , (λ σ pr → transEQREL σ (RenNorm.fusion (ρA σ pr) (step refl) _ _ (proj₁ ρR))
                                          ((proj₂ ∘ proj₂) ρR σ pr)) ]
    ; RelEnvWk = λ inc {ρA} ρR →
                            (λ σ pr → wk^EQREL σ inc (proj₁ ρR σ pr))
                          , (λ σ pr {Θ} inc′ →
                               transEQREL σ (EqNorm.related (ρA σ pr)
                               (λ σ pr → transEQREL σ (wk^2 σ inc inc′ (proj₁ ρR σ pr))
                                                      (wk^EQREL σ (trans inc inc′) (proj₁ ρR σ pr))))
                               (transEQREL σ ((proj₁ ∘ proj₂) ρR σ pr (trans inc inc′))
                               (symEQREL σ (wk^2 σ inc inc′ (reflEQREL σ (symEQREL σ $ (proj₂ ∘ proj₂) ρR σ pr))))))
                          , (λ σ pr → (proj₁ ∘ proj₂) ρR σ pr inc)
    ; R⟦var⟧   = λ v _ _ _ ρR → (proj₂ ∘ proj₂) ρR _ v
    ; R⟦$⟧     = λ _ _ _ _ _ _ r → r refl
    ; R⟦λ⟧     = λ _ _ _ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ _ _ _ → tt
    ; R⟦tt⟧    = λ _ _ _ _ → trivial
    ; R⟦ff⟧    = λ _ _ _ _ → trivial
    ; R⟦ifte⟧  = ifteSubstNorm
    }

\end{code}
