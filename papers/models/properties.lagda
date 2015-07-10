\section{Properties of these \AR{Semantics}}

\begin{code}
module properties where

open import Level
open import Data.Unit
open import Data.Product
open import Function
open import models

record Relatable
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB : Level}
  {EnvA : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {ModA : (Γ : Con) (σ : ty) → Set ℓ^MA}
  (semA : Semantics EnvA ModA)
  {EnvB : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {ModB : (Γ : Con) (σ : ty) → Set ℓ^MB}
  (semB : Semantics EnvB ModB)
  {ℓ^RE ℓ^RM ℓ^REAB : Level}
  (RelEnvAB : {Γ : Con} {σ : ty} (eA : EnvA Γ σ) (eB : EnvB Γ σ) → Set ℓ^REAB)
  (RelEnv : {Δ Γ : Con} (eA : Δ [ EnvA ] Γ) (eB : Δ [ EnvB ] Γ) → Set ℓ^RE)
  (RelMod : {Γ : Con} {σ : ty} (mA : ModA Γ σ) (mB : ModB Γ σ) → Set ℓ^RM)
  : Set (ℓ^RE ⊔ ℓ^RM ⊔ ℓ^EA ⊔ ℓ^EB ⊔ ℓ^MA ⊔ ℓ^MB ⊔ ℓ^REAB) where
  module SemA = Semantics semA
  module SemB = Semantics semB
  field
    RelEnv∙ : {Γ Δ : Con} {σ : ty} {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ}
              {uA : EnvA Δ σ} {uB : EnvB Δ σ} (ρR : RelEnv ρA ρB) (uR : RelEnvAB uA uB) →
               RelEnv ([ EnvA ] ρA `∙ uA) ([ EnvB ] ρB `∙ uB)
    RelEnvWk : {Γ Δ Θ : Con} (inc : Δ ⊆ Θ)
               {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
               RelEnv (wk[ SemA.wk ] inc ρA) (wk[ SemB.wk ] inc ρB)
    R⟦var⟧  : {Γ Δ : Con} {σ : ty} (v : σ ∈ Γ)
              {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ} (ρR : RelEnv ρA ρB) →
              RelMod (semA ⊨⟦ `var v ⟧ ρA) (semB ⊨⟦ `var v ⟧ ρB)

    R⟦$⟧    : {Γ Δ : Con} {σ τ : ty} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ)
              (ρA : Δ [ EnvA ] Γ) (ρB : Δ [ EnvB ] Γ)  (ρR : RelEnv ρA ρB) →
              RelMod (semA ⊨⟦ f ⟧ ρA) (semB ⊨⟦ f ⟧ ρB) → 
              RelMod (semA ⊨⟦ t ⟧ ρA) (semB ⊨⟦ t ⟧ ρB) →
              RelMod (semA ⊨⟦ f `$ t ⟧ ρA) (semB ⊨⟦ f `$ t ⟧ ρB)
    R⟦λ⟧    : {Γ Δ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ)
              (ρA : Δ [ EnvA ] Γ) (ρB : Δ [ EnvB ] Γ) (ρR : RelEnv ρA ρB) →
              (r : {Θ : Con} (inc : Δ ⊆ Θ) {uA : EnvA Θ σ} {uB : EnvB Θ σ} (uR : RelEnvAB uA uB) →
                  RelMod (semA ⊨⟦ t ⟧ ([ EnvA ] wk[ SemA.wk ] inc ρA `∙ uA))
                         (semB ⊨⟦ t ⟧ ([ EnvB ] wk[ SemB.wk ] inc ρB `∙ uB))) →
              RelMod (semA ⊨⟦ `λ t ⟧ ρA) (semB ⊨⟦ `λ t ⟧ ρB)
    R⟦⟨⟩⟧   : {Γ Δ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Δ [ EnvB ] Γ) (ρR : RelEnv ρA ρB) →
              RelMod (semA ⊨⟦ `⟨⟩ ⟧ ρA) (semB ⊨⟦ `⟨⟩ ⟧ ρB)
    R⟦tt⟧   : {Γ Δ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Δ [ EnvB ] Γ) (ρR : RelEnv ρA ρB) →
              RelMod (semA ⊨⟦ `tt ⟧ ρA) (semB ⊨⟦ `tt ⟧ ρB)
    R⟦ff⟧   : {Γ Δ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Δ [ EnvB ] Γ) (ρR : RelEnv ρA ρB) →
            RelMod (semA ⊨⟦ `ff ⟧ ρA) (semB ⊨⟦ `ff ⟧ ρB)
    R⟦ifte⟧ : {Γ Δ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
            (ρA : Δ [ EnvA ] Γ) (ρB : Δ [ EnvB ] Γ) (ρR : RelEnv ρA ρB) →
            RelMod (semA ⊨⟦ b ⟧ ρA) (semB ⊨⟦ b ⟧ ρB) → 
            RelMod (semA ⊨⟦ l ⟧ ρA) (semB ⊨⟦ l ⟧ ρB) →
            RelMod (semA ⊨⟦ r ⟧ ρA) (semB ⊨⟦ r ⟧ ρB) →
            RelMod (semA ⊨⟦ `ifte b l r ⟧ ρA) (semB ⊨⟦ `ifte b l r ⟧ ρB)

module Related
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB : Level}
  {EnvA : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {ModA : (Γ : Con) (σ : ty) → Set ℓ^MA}
  {semA : Semantics EnvA ModA}
  {EnvB : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {ModB : (Γ : Con) (σ : ty) → Set ℓ^MB}
  {semB : Semantics EnvB ModB}
  {ℓ^RE ℓ^RM ℓ^REAB : Level}
  {RelEnvAB : {Γ : Con} {σ : ty} (eA : EnvA Γ σ) (eB : EnvB Γ σ) → Set ℓ^REAB}
  {RelEnv : {Δ Γ : Con} (eA : Δ [ EnvA ] Γ) (eB : Δ [ EnvB ] Γ) → Set ℓ^RE}
  {RelMod : {Γ : Con} {σ : ty} (mA : ModA Γ σ) (mB : ModB Γ σ) → Set ℓ^RM}
  (rel : Relatable semA semB RelEnvAB RelEnv RelMod)
  where
  open Relatable rel

  related : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρA : Δ [ EnvA ] Γ} {ρB : Δ [ EnvB ] Γ}
            (ρR : RelEnv ρA ρB) → RelMod (semA ⊨⟦ t ⟧ ρA) (semB ⊨⟦ t ⟧ ρB)
  related (`var v)      ρR = R⟦var⟧ v ρR
  related (f `$ t)      ρR = R⟦$⟧ f t _ _ ρR (related f ρR) (related t ρR)
  related (`λ t)        ρR = R⟦λ⟧ t _ _ ρR $ λ inc uR → related t (RelEnv∙ (RelEnvWk inc ρR) uR)
  related `⟨⟩           ρR = R⟦⟨⟩⟧ _ _ ρR
  related `tt           ρR = R⟦tt⟧ _ _ ρR
  related `ff           ρR = R⟦ff⟧ _ _ ρR
  related (`ifte b l r) ρR = R⟦ifte⟧ b l r _ _ ρR (related b ρR) (related l ρR) (related r ρR)


open import Relation.Binary.PropositionalEquality
            as PEq
            hiding ([_] ; trans)
            renaming (refl to trivial)


RelatableRenamingSubstitution :
  Relatable Renaming Substitution
            (λ v t → `var v ≡ t)
            (λ ρA ρB → (σ : ty) (pr : σ ∈ _) → `var (ρA σ pr) ≡ ρB σ pr)
            _≡_
RelatableRenamingSubstitution =
  record
    { RelEnv∙   = λ ρR uR → [ uR , ρR ]
    ; RelEnvWk  = λ inc ρR σ pr → cong (wk^⊢ inc) (ρR σ pr)
    ; R⟦var⟧    = λ v ρR → ρR _ v
    ; R⟦$⟧      = λ _ _ _ _ _ → cong₂ _`$_
    ; R⟦λ⟧      = λ _ _ _ ρR r → cong `λ (r (step refl) trivial)
    ; R⟦⟨⟩⟧     = λ _ _ _ → trivial
    ; R⟦tt⟧     = λ _ _ _ → trivial
    ; R⟦ff⟧     = λ _ _ _ → trivial
    ; R⟦ifte⟧   = λ _ _ _ _ _ _ eqb eql → cong₂ (uncurry `ifte) (cong₂ _,_ eqb eql)
    }


EQREL : (Γ : Con) (σ : ty) (T U : Γ ⊨^βιξη σ) → Set
EQREL Γ `Unit     T U = ⊤
EQREL Γ `Bool     T U = T ≡ U
EQREL Γ (σ `→ τ)  T U = {Δ : Con} (inc : Γ ⊆ Δ) {V W : Δ ⊨^βιξη σ} (EQVW : EQREL Δ σ V W) →
                        EQREL Δ τ (T inc V) (U inc W)

wk^EQREL : {Δ Γ : Con} (σ : ty) (inc : Γ ⊆ Δ) {T U : Γ ⊨^βιξη σ} →
           EQREL Γ σ T U → EQREL Δ σ (wk^βιξη σ inc T) (wk^βιξη σ inc U)
wk^EQREL `Unit     inc eq = tt
wk^EQREL `Bool     inc eq = cong (wk^nf inc) eq
wk^EQREL (σ `→ τ)  inc eq = λ inc′ eqVW → eq (trans inc inc′) eqVW

symEQREL : {Γ : Con} (σ : ty) {S T : Γ ⊨^βιξη σ} →
           EQREL Γ σ S T → EQREL Γ σ T S
symEQREL `Unit     eq = tt
symEQREL `Bool     eq = PEq.sym eq
symEQREL (σ `→ τ)  eq = λ inc eqVW → symEQREL τ (eq inc (symEQREL σ eqVW))

mutual

  transEQREL : {Γ : Con} (σ : ty) {S T U : Γ ⊨^βιξη σ} →
               EQREL Γ σ S T → EQREL Γ σ T U → EQREL Γ σ S U
  transEQREL `Unit     eq₁ eq₂ = tt
  transEQREL `Bool     eq₁ eq₂ = PEq.trans eq₁ eq₂
  transEQREL (σ `→ τ)  eq₁ eq₂ =
    λ inc eqVW → transEQREL τ (eq₁ inc (reflEQREL σ eqVW)) (eq₂ inc eqVW)

  -- We are in PER so reflEQREL is not provable
  -- but as soon as EQREL σ V W then EQREL σ V V
  reflEQREL : {Γ : Con} (σ : ty) {S T : Γ ⊨^βιξη σ} →
              EQREL Γ σ S T → EQREL Γ σ S S
  reflEQREL σ eq = transEQREL σ eq (symEQREL σ eq)

mutual

  reify^EQREL : {Γ : Con} (σ : ty) {T U : Γ ⊨^βιξη σ} (EQTU : EQREL Γ σ T U) → reify^βιξη σ T ≡ reify^βιξη σ U
  reify^EQREL `Unit     EQTU = trivial
  reify^EQREL `Bool     EQTU = EQTU
  reify^EQREL (σ `→ τ)  EQTU = cong `λ $ reify^EQREL τ $ EQTU (step refl) $ reflect^EQREL σ trivial

  reflect^EQREL : {Γ : Con} (σ : ty) {t u : Γ ⊢^ne σ} (eq : t ≡ u) → EQREL Γ σ (reflect^βιξη σ t) (reflect^βιξη σ u)
  reflect^EQREL `Unit     eq = tt
  reflect^EQREL `Bool     eq = cong `embed eq
  reflect^EQREL (σ `→ τ)  eq = λ inc rel → reflect^EQREL τ $ cong₂ _`$_ (cong (wk^ne inc) eq) (reify^EQREL σ rel)

ifteRelNorm :
      {Γ Δ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      (ρA ρB : Δ [ _⊨^βιξη_ ] Γ) →
      ((σ₁ : ty) (pr : σ₁ ∈ Γ) → EQREL Δ σ₁ (ρA σ₁ pr) (ρB σ₁ pr)) →
      Normalise^βιξη ⊨⟦ b ⟧ ρA ≡ Normalise^βιξη ⊨⟦ b ⟧ ρB →
      EQREL Δ σ (Normalise^βιξη ⊨⟦ l ⟧ ρA) (Normalise^βιξη ⊨⟦ l ⟧ ρB) →
      EQREL Δ σ (Normalise^βιξη ⊨⟦ r ⟧ ρA) (Normalise^βιξη ⊨⟦ r ⟧ ρB) →
      EQREL Δ σ (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρA)
      (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρB)
ifteRelNorm b l r ρA ρB ρR eqb eql eqr
  with Normalise^βιξη ⊨⟦ b ⟧ ρA
     | Normalise^βιξη ⊨⟦ b ⟧ ρB
ifteRelNorm b l r ρA ρB ρR trivial eql eqr | `embed t | `embed .t =
  reflect^EQREL _ (cong₂ (uncurry `ifte) (cong₂ _,_ trivial (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteRelNorm b l r ρA ρB ρR () eql eqr | `embed t | `tt
ifteRelNorm b l r ρA ρB ρR () eql eqr | `embed t | `ff
ifteRelNorm b l r ρA ρB ρR () eql eqr | `tt | `embed t
ifteRelNorm b l r ρA ρB ρR trivial eql eqr | `tt | `tt = eql
ifteRelNorm b l r ρA ρB ρR () eql eqr | `tt | `ff
ifteRelNorm b l r ρA ρB ρR () eql eqr | `ff | `embed t
ifteRelNorm b l r ρA ρB ρR () eql eqr | `ff | `tt
ifteRelNorm b l r ρA ρB ρR trivial eql eqr | `ff | `ff = eqr

RelatableNormalise :
  Relatable Normalise^βιξη Normalise^βιξη
            (EQREL _ _) (λ ρA ρB → (σ : ty) (pr : σ ∈ _) → EQREL _ σ (ρA σ pr) (ρB σ pr)) (EQREL _ _)
RelatableNormalise =
  record
    { RelEnv∙  = λ ρR uR → [ uR , ρR ]
    ; RelEnvWk = λ inc ρR σ pr → wk^EQREL σ inc (ρR σ pr)
    ; R⟦var⟧   = λ v ρR → ρR _ v
    ; R⟦$⟧     = λ _ _ _ _ _ f → f refl
    ; R⟦λ⟧     = λ _ _ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ _ _ → tt
    ; R⟦tt⟧    = λ _ _ _ → trivial
    ; R⟦ff⟧    = λ _ _ _ → trivial
    ; R⟦ifte⟧  = ifteRelNorm
    }

\end{code}
