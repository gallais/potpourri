
\begin{code}
module fusion where

open import Level
open import Data.Unit
open import Data.Product
open import Function
open import models
open import Relation.Binary.On
open import Relation.Binary.PropositionalEquality renaming (refl to trivial) using (_≡_ ; cong ; cong₂)

module Fusion
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^RM : Level}
  {EnvA   : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB   : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC   : (Γ : Con) (σ : ty) → Set ℓ^EC}
  {ModA   : (Γ : Con) (σ : ty) → Set ℓ^MA}
  {ModB   : (Γ : Con) (σ : ty) → Set ℓ^MB}
  {ModC   : (Γ : Con) (σ : ty) → Set ℓ^MC}
  (semA   : Semantics EnvA ModA)
  (semB   : Semantics EnvB ModB)
  (semC   : Semantics EnvC ModC)
  (RelEnv : {Δ Γ : Con} {σ : ty} (eA : EnvA Γ σ) (ρB : Δ [ EnvB ] Γ) (eC : EnvC Δ σ) → Set ℓ^RE)
  (RelMod : {Γ : Con} {σ : ty} (mB : ModB Γ σ) (mC : ModC Γ σ) → Set ℓ^RM)
  (ModA⊢  : {Γ : Con} {σ : ty} (m : ModA Γ σ) → Γ ⊢ σ)
  (Rwk     : {Δ Γ : Con} {σ : ty} (eA : EnvA Γ σ) (ρB : Δ [ EnvB ] Γ) (eC : EnvC Δ σ) →
             {σ : ty} (uB : EnvB Δ σ) →
             RelEnv eA ρB eC →
             let open Semantics semA
             in RelEnv (wk (step refl) eA) ([ EnvB ] ρB `∙ uB) eC)
  (Rwk2    : {Δ Γ : Con} {σ : ty} (eA : EnvA Γ σ) (ρB : Δ [ EnvB ] Γ) (eC : EnvC Δ σ) →
             {Θ : Con} (inc : Δ ⊆ Θ) → RelEnv eA ρB eC →
             let module SemB = Semantics semB
                 module SemC = Semantics semC
             in RelEnv eA (wk[ SemB.wk ] inc ρB) (SemC.wk inc eC))
  (R⟦var⟧  : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ)
             (ρR : (σ : ty) (pr : σ ∈ Γ) → RelEnv (ρA σ pr) ρB (ρC σ pr)) →
             RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `var v ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `var v ⟧ ρC))
  (R⟦$⟧    : {Γ Δ Θ : Con} {σ τ : ty} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ)
            (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : (σ : ty) (pr : σ ∈ Γ) → RelEnv (ρA σ pr) ρB (ρC σ pr)) →
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ f ⟧ ρA) ⟧ ρB) (semC ⊨⟦ f ⟧ ρC) → 
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ t ⟧ ρC) →
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ f `$ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ f `$ t ⟧ ρC))
  (R⟦λ⟧    : {Γ Δ Θ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ)
             (ρR : (σ : ty) (pr : σ ∈ Γ) → RelEnv (ρA σ pr) ρB (ρC σ pr)) →
             (r : {E : Con} (inc : Θ ⊆ E) (uB : EnvB E σ) (uC : EnvC E σ) →
                  let module SemA = Semantics semA
                      module SemB = Semantics semB
                      module SemC = Semantics semC
                  in
                  (uR : RelEnv (SemA.embed σ here!) ([ EnvB ] wk[ SemB.wk ] inc ρB `∙ uB) uC) →
                  RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ t ⟧ ([ EnvA ] wk[ SemA.wk ] (step refl) ρA `∙ SemA.embed σ here!)) ⟧
                              ([ EnvB ] wk[ SemB.wk ] inc ρB `∙ uB))
                        (semC ⊨⟦ t ⟧ ([ EnvC ] wk[ SemC.wk ] inc ρC `∙ uC))) →
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `λ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `λ t ⟧ ρC))
  (R⟦⟨⟩⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : (σ : ty) (pr : σ ∈ Γ) → RelEnv (ρA σ pr) ρB (ρC σ pr)) →
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `⟨⟩ ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `⟨⟩ ⟧ ρC))
  (R⟦tt⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : (σ : ty) (pr : σ ∈ Γ) → RelEnv (ρA σ pr) ρB (ρC σ pr)) →
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `tt ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `tt ⟧ ρC))
  (R⟦ff⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : (σ : ty) (pr : σ ∈ Γ) → RelEnv (ρA σ pr) ρB (ρC σ pr)) →
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `ff ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `ff ⟧ ρC))
  (R⟦ifte⟧ : {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
            (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ) →
             (ρR : (σ : ty) (pr : σ ∈ Γ) → RelEnv (ρA σ pr) ρB (ρC σ pr)) →
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ b ⟧ ρA) ⟧ ρB) (semC ⊨⟦ b ⟧ ρC) → 
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ l ⟧ ρA) ⟧ ρB) (semC ⊨⟦ l ⟧ ρC) →
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ r ⟧ ρA) ⟧ ρB) (semC ⊨⟦ r ⟧ ρC) →
            RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `ifte b l r ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `ifte b l r ⟧ ρC))
  where

  extend : ∀ {Γ Δ Θ σ} {ρA : Δ [ EnvA ] Γ} {ρB : Θ [ EnvB ] Δ}
             {ρC : Θ [ EnvC ] Γ} {uB : EnvB Θ σ} {uC : EnvC Θ σ} →
             (∀ σ₁ (pr : σ₁ ∈ Γ) → RelEnv (ρA σ₁ pr) ρB (ρC σ₁ pr)) →
             RelEnv (Semantics.embed semA σ here!) ([ EnvB ] ρB `∙ uB) uC →
           ∀ σ₁ (pr : σ₁ ∈ Γ ∙ σ) →
             RelEnv
           (([ EnvA ]
             (λ σ₂ pr₁ → Semantics.wk semA (λ σ₃ → there) (ρA σ₂ pr₁)) `∙
             Semantics.embed semA σ here!)
            σ₁ pr)
           ([ EnvB ] ρB `∙ uB) (([ EnvC ] ρC `∙ uC) σ₁ pr)
  extend ρR uR σ here! = uR
  extend ρR uR σ₁ (there pr) = Rwk _ _ _ _ (ρR σ₁ pr)

  fusion :
    {Γ Δ Θ : Con} {σ : ty}
    (t : Γ ⊢ σ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) (ρC : Θ [ EnvC ] Γ)
             (ρR : (σ : ty) (pr : σ ∈ Γ) → RelEnv (ρA σ pr) ρB (ρC σ pr)) →
    RelMod (semB ⊨⟦ ModA⊢ (semA ⊨⟦ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ t ⟧ ρC)
  fusion (`var v)      ρA ρB ρC ρR = R⟦var⟧ v ρA ρB ρC ρR
  fusion (f `$ t)      ρA ρB ρC ρR = R⟦$⟧ f t ρA ρB ρC ρR (fusion f ρA ρB ρC ρR) (fusion t ρA ρB ρC ρR)
  fusion (`λ t)        ρA ρB ρC ρR = R⟦λ⟧ t ρA ρB ρC ρR $ λ inc uB uC uR →
                                     fusion t _ _ ([ EnvC ] _ `∙ uC) (extend {!!} uR)
  fusion `⟨⟩           ρA ρB ρC ρR = R⟦⟨⟩⟧ ρA ρB ρC ρR
  fusion `tt           ρA ρB ρC ρR = R⟦tt⟧ ρA ρB ρC ρR
  fusion `ff           ρA ρB ρC ρR = R⟦ff⟧ ρA ρB ρC ρR
  fusion (`ifte b l r) ρA ρB ρC ρR = R⟦ifte⟧ b l r ρA ρB ρC ρR (fusion b ρA ρB ρC ρR) (fusion l ρA ρB ρC ρR) (fusion r ρA ρB ρC ρR)

module SyntacticFusion 
  {ℓ^EA ℓ^EB ℓ^EC : Level}
  {EnvA  : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB  : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC  : (Γ : Con) (σ : ty) → Set ℓ^EC}
  (synA : Syntactic EnvA) (synB : Syntactic EnvB) (synC : Syntactic EnvC)
  (Rwk     : {Δ Γ : Con} {σ : ty} (eA : EnvA Γ σ) (ρB : Δ [ EnvB ] Γ) (eC : EnvC Δ σ) →
             {σ : ty} (uB : EnvB Δ σ) →
             syntactic synB ⊨⟦ Semantics.⟦var⟧ (syntactic synA) eA ⟧ ρB
                                       ≡ Semantics.⟦var⟧ (syntactic synC) eC →
             let open Semantics (syntactic synA)
             in syntactic synB ⊨⟦ ⟦var⟧ (wk (step refl) eA) ⟧ ([ EnvB ] ρB `∙ uB)
              ≡ Semantics.⟦var⟧ (syntactic synC) eC)
  (Rwk2    : {Δ Γ : Con} {σ : ty} (eA : EnvA Γ σ) (ρB : Δ [ EnvB ] Γ) (eC : EnvC Δ σ) →
             {Θ : Con} (inc : Δ ⊆ Θ) →
             syntactic synB ⊨⟦ Semantics.⟦var⟧ (syntactic synA) eA ⟧ ρB
                                       ≡ Semantics.⟦var⟧ (syntactic synC) eC →
             let module SemB = Semantics (syntactic synB)
                 module SemC = Semantics (syntactic synC)
             in syntactic synB ⊨⟦ Semantics.⟦var⟧ (syntactic synA) eA ⟧ (wk[ SemB.wk ] inc ρB)
              ≡ SemC.⟦var⟧ (SemC.wk inc eC))
  where

  module Instance = Fusion (syntactic synA) (syntactic synB) (syntactic synC)
                           (λ a ρB c → syntactic synB ⊨⟦ Semantics.⟦var⟧ (syntactic synA) a ⟧ ρB
                                       ≡ Semantics.⟦var⟧ (syntactic synC) c)
                           _≡_ id Rwk Rwk2 (λ v _ _ _ r → r _ v) (λ _ _ _ _ _ _ → cong₂ _`$_)
                           (λ t _ _ _ ρR r → cong `λ (r (step refl) (Semantics.embed (syntactic synB) _ here!)
                                                    (Semantics.embed (syntactic synC) _ here!)
                                                    {!!}))
                           (λ _ _ _ _ → trivial) (λ _ _ _ _ → trivial) (λ _ _ _ _ → trivial)
                           (λ _ _ _ _ _ _ _ eqb eql → cong₂ (uncurry `ifte) $ cong₂ _,_ eqb eql)

syntacticRenaming : Syntactic (flip _∈_)
syntacticRenaming = record { wk = wk^∈ ; embed = λ _ → id ; ⟦var⟧ = `var }

syntacticSubstitution : Syntactic _⊢_
syntacticSubstitution = record { wk = wk^⊢ ; embed = λ _ → `var ; ⟦var⟧ = id }

module RenamingFusion =
  SyntacticFusion syntacticRenaming syntacticRenaming syntacticRenaming
                  (λ _ _ _ _ → id) {!!}

{-
module RenamingSubstitutionFusion =
  SyntacticFusion syntacticRenaming syntacticSubstitution syntacticSubstitution
                  (λ ρB ρA σ pr → ρB σ $ ρA σ pr) (λ _ _ _ → trivial)
module SubstitutionRenamingFusion =
  SyntacticFusion syntacticSubstitution syntacticRenaming syntacticSubstitution
                  (λ ρB ρA σ pr → wk^⊢ ρB $ ρA σ pr) (λ _ _ _ → trivial)
module SubstitutionFusion =
  SyntacticFusion syntacticSubstitution syntacticSubstitution syntacticSubstitution
                  (λ ρB ρA σ pr → Substitution ⊨⟦ ρA σ pr ⟧ ρB) (λ _ _ _ → trivial)

mutual

  erase-⊢^ne : {Γ : Con} {σ : ty} (t : Γ ⊢^ne σ) → Γ ⊢ σ
  erase-⊢^ne (`var v)      = `var v
  erase-⊢^ne (t `$ u)      = erase-⊢^ne t `$ erase-⊢^nf u
  erase-⊢^ne (`ifte b l r) = `ifte (erase-⊢^ne b) (erase-⊢^nf l) (erase-⊢^nf r)

  erase-⊢^nf : {Γ : Con} {σ : ty} (t : Γ ⊢^nf σ) → Γ ⊢ σ
  erase-⊢^nf (`embed t) = erase-⊢^ne t
  erase-⊢^nf `⟨⟩        = `⟨⟩
  erase-⊢^nf `tt        = `tt
  erase-⊢^nf `ff        = `ff
  erase-⊢^nf (`λ t)     = `λ (erase-⊢^nf t)


EQREL : (Γ : Con) (σ : ty) (T U : Γ ⊨^βιξη σ) → Set
EQREL Γ `Unit     T U = ⊤
EQREL Γ `Bool     T U = T ≡ U
EQREL Γ (σ `→ τ)  T U = {Δ : Con} (inc : Γ ⊆ Δ) {V W : Δ ⊨^βιξη σ} (EQVW : EQREL Δ σ V W) →
                        EQREL Δ τ (T inc V) (U inc W)

mutual

  reify^EQREL : {Γ : Con} (σ : ty) {T U : Γ ⊨^βιξη σ} (EQTU : EQREL Γ σ T U) → reify^βιξη σ T ≡ reify^βιξη σ U
  reify^EQREL `Unit     EQTU = trivial
  reify^EQREL `Bool     EQTU = EQTU
  reify^EQREL (σ `→ τ)  EQTU = cong `λ $ reify^EQREL τ $ EQTU (step refl) $ reflect^EQREL σ trivial

  reflect^EQREL : {Γ : Con} (σ : ty) {t u : Γ ⊢^ne σ} (eq : t ≡ u) → EQREL Γ σ (reflect^βιξη σ t) (reflect^βιξη σ u)
  reflect^EQREL `Unit     eq = tt
  reflect^EQREL `Bool     eq = cong `embed eq
  reflect^EQREL (σ `→ τ)  eq = λ inc rel → reflect^EQREL τ $ cong₂ _`$_ (cong (wk^ne inc) eq) (reify^EQREL σ rel)


-- we should be able to get this from instantiating another
-- thing...
refl^EQREL :
  {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ)
  {ρ₁ ρ₂ : Δ [ _⊨^βιξη_ ] Γ} (ρ : ρ₁ R[ EQREL ] ρ₂) →
  EQREL Δ σ (Normalise^βιξη ⊨⟦ t ⟧ ρ₁) (Normalise^βιξη ⊨⟦ t ⟧ ρ₂)
refl^EQREL (`var v)       ρ = ρ _ v
refl^EQREL (f `$ t)       ρ = refl^EQREL f ρ refl (refl^EQREL t ρ)
refl^EQREL (`λ t)         ρ = λ inc rvw → refl^EQREL t (wkR[ {!!} , {!!} , {!!} ] inc {!!} )
refl^EQREL `⟨⟩            ρ = tt
refl^EQREL `tt            ρ = trivial
refl^EQREL `ff            ρ = trivial
refl^EQREL (`ifte b l r)  ρ = {!!}

module NormalisationFusion =
  Fusion Normalise^βιξη Normalise^βιξη Normalise^βιξη {!!} (EQREL _ _) (erase-⊢^nf ∘ reify^βιξη _)
         (λ ρB ρA σ pr → Normalise^βιξη ⊨⟦ erase-⊢^nf (reify^βιξη σ $ ρA σ pr) ⟧ ρB)
         (λ v ρA ρB → refl^EQREL (erase-⊢^nf (reify^βιξη _ $ ρA _ v)) {!!}) {!!}
         (λ _ _ → trivial) {!!}
         (λ _ _ → tt) (λ _ _ → trivial) (λ _ _ → trivial)
         (λ _ _ _ _ _ eqb eql eqr → {!!})
         
module NormalisationSubstitutionFusion =
  Fusion Substitution Normalise^βιξη Normalise^βιξη {!!} (EQREL _ _)
         id (λ ρB ρA σ pr → Normalise^βιξη ⊨⟦ ρA σ pr ⟧ ρB) (λ v ρA ρB → {!!}) {!!}
--         id (λ ρB ρA σ pr → Normalise^βιξη ⊨⟦ ρA σ pr ⟧ ρB) (λ _ _ _ → trivial)
  --       (λ _ _ _ _ eqf eqt → {!!})
    --     (λ _ _ → trivial) (λ _ _ → trivial) (λ _ _ → trivial)
      --   (λ _ _ _ _ _ eqb eql eqr → {!!})
-}
\end{code}
