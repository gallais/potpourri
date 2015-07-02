
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
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^R : Level}
  {EnvA   : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB   : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC   : (Γ : Con) (σ : ty) → Set ℓ^EC}
  {ModA   : (Γ : Con) (σ : ty) → Set ℓ^MA}
  {ModB   : (Γ : Con) (σ : ty) → Set ℓ^MB}
  {ModC   : (Γ : Con) (σ : ty) → Set ℓ^MC}
  (semA   : Semantics EnvA ModA)
  (semB   : Semantics EnvB ModB)
  (semC   : Semantics EnvC ModC)
  (Rel    : {Γ : Con} {σ : ty} (mB : ModB Γ σ) (mC : ModC Γ σ) → Set ℓ^R)
  (ModA⊢  : {Γ : Con} {σ : ty} (m : ModA Γ σ) → Γ ⊢ σ)
  (_B∘A_  : {Γ Δ Θ : Con} (ρB : Θ [ EnvB ] Δ) (ρA : Δ [ EnvA ] Γ) → Θ [ EnvC ] Γ)
  (⟦var⟧  : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) →
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `var v ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `var v ⟧ (ρB B∘A ρA)))
  (⟦$⟧    : {Γ Δ Θ : Con} {σ τ : ty} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) →
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ f ⟧ ρA) ⟧ ρB) (semC ⊨⟦ f ⟧ (ρB B∘A ρA)) → 
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ t ⟧ (ρB B∘A ρA)) →
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ f `$ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ f `$ t ⟧ (ρB B∘A ρA)))
  (⟦⟨⟩⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) →
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `⟨⟩ ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `⟨⟩ ⟧ (ρB B∘A ρA)))
  (⟦tt⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) →
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `tt ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `tt ⟧ (ρB B∘A ρA)))
  (⟦ff⟧   : {Γ Δ Θ : Con} (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) →
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `ff ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `ff ⟧ (ρB B∘A ρA)))
  (⟦ifte⟧ : {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) →
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ b ⟧ ρA) ⟧ ρB) (semC ⊨⟦ b ⟧ (ρB B∘A ρA)) → 
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ l ⟧ ρA) ⟧ ρB) (semC ⊨⟦ l ⟧ (ρB B∘A ρA)) →
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ r ⟧ ρA) ⟧ ρB) (semC ⊨⟦ r ⟧ (ρB B∘A ρA)) →
            Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ `ifte b l r ⟧ ρA) ⟧ ρB) (semC ⊨⟦ `ifte b l r ⟧ (ρB B∘A ρA)))
  where

  fusion :
    {Γ Δ Θ : Con} {σ : ty}
    (t : Γ ⊢ σ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) →
    Rel (semB ⊨⟦ ModA⊢ (semA ⊨⟦ t ⟧ ρA) ⟧ ρB) (semC ⊨⟦ t ⟧ (ρB B∘A ρA))
  fusion (`var v)      ρA ρB = ⟦var⟧ v ρA ρB
  fusion (f `$ t)      ρA ρB = ⟦$⟧ f t ρA ρB (fusion f ρA ρB) (fusion t ρA ρB)
  fusion (`λ t)        ρA ρB = {!!}
  fusion `⟨⟩           ρA ρB = ⟦⟨⟩⟧ ρA ρB
  fusion `tt           ρA ρB = ⟦tt⟧ ρA ρB
  fusion `ff           ρA ρB = ⟦ff⟧ ρA ρB
  fusion (`ifte b l r) ρA ρB = ⟦ifte⟧ b l r ρA ρB (fusion b ρA ρB) (fusion l ρA ρB) (fusion r ρA ρB)


record Syntactic {ℓ : Level} (Env : (Γ : Con) (σ : ty) → Set ℓ) : Set ℓ where
  field
    wk    : {Γ Δ : Con} {σ : ty} → Γ ⊆ Δ → Env Γ σ → Env Δ σ
    embed : {Γ : Con} (σ : ty) → σ ∈ Γ → Env Γ σ
    var   : {Γ : Con} {σ : ty} → Env Γ σ → Γ ⊢ σ


syntactic :
  {ℓ : Level} {Env : (Γ : Con) (σ : ty) → Set ℓ}
  (syn : Syntactic Env) → Semantics Env _⊢_
syntactic syn =
  let open Syntactic syn in
  record
    { wk     = wk
    ; embed  = embed
    ; ⟦var⟧  = var
    ; _⟦$⟧_  = _`$_
    ; ⟦λ⟧    = λ t → `λ (t (step refl) (embed _ here!))
    ; ⟦⟨⟩⟧   = `⟨⟩
    ; ⟦tt⟧   = `tt
    ; ⟦ff⟧   = `ff
    ; ⟦ifte⟧ = `ifte
    }

module SyntacticFusion 
  {ℓ^EA ℓ^EB ℓ^EC : Level}
  {EnvA  : (Γ : Con) (σ : ty) → Set ℓ^EA}
  {EnvB  : (Γ : Con) (σ : ty) → Set ℓ^EB}
  {EnvC  : (Γ : Con) (σ : ty) → Set ℓ^EC}
  (synA : Syntactic EnvA) (synB : Syntactic EnvB) (synC : Syntactic EnvC)
  (_B∘A_ : {Γ Δ Θ : Con} (ρB : Θ [ EnvB ] Δ) (ρA : Δ [ EnvA ] Γ) → Θ [ EnvC ] Γ)
  (⟦var⟧ : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) (ρA : Δ [ EnvA ] Γ) (ρB : Θ [ EnvB ] Δ) →
           syntactic synB ⊨⟦ syntactic synA ⊨⟦ `var v ⟧ ρA ⟧ ρB ≡ syntactic synC ⊨⟦ `var v ⟧ (ρB B∘A ρA))
  where

  module Instance = Fusion (syntactic synA) (syntactic synB) (syntactic synC) _≡_
                           id _B∘A_ ⟦var⟧ (λ _ _ _ _ → cong₂ _`$_)
                           (λ _ _ → trivial) (λ _ _ → trivial) (λ _ _ → trivial)
                           (λ _ _ _ _ _ eqb eql → cong₂ (uncurry `ifte) $ cong₂ _,_ eqb eql)


syntacticRenaming : Syntactic (flip _∈_)
syntacticRenaming = record { wk = wk^∈ ; embed = λ _ → id ; var = `var }

syntacticSubstitution : Syntactic _⊢_
syntacticSubstitution = record { wk = wk^⊢ ; embed = λ _ → `var ; var = id }

module RenamingFusion =
  SyntacticFusion syntacticRenaming syntacticRenaming syntacticRenaming
                  (flip trans) (λ _ _ _ → trivial)
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


EQREL : (Γ : Con) (σ : ty) (T U : Γ ⊨^βξη σ) → Set
EQREL Γ `Unit     T U = ⊤
EQREL Γ `Bool     T U = T ≡ U
EQREL Γ (σ `→ τ)  T U = {Δ : Con} (inc : Γ ⊆ Δ) {V W : Δ ⊨^βξη σ} (EQVW : EQREL Δ σ V W) →
                        EQREL Δ τ (T inc V) (U inc W)

mutual

  reify^EQREL : {Γ : Con} (σ : ty) {T U : Γ ⊨^βξη σ} (EQTU : EQREL Γ σ T U) → reify^βξη σ T ≡ reify^βξη σ U
  reify^EQREL `Unit     EQTU = trivial
  reify^EQREL `Bool     EQTU = EQTU
  reify^EQREL (σ `→ τ)  EQTU = cong `λ $ reify^EQREL τ $ EQTU (step refl) $ reflect^EQREL σ trivial

  reflect^EQREL : {Γ : Con} (σ : ty) {t u : Γ ⊢^ne σ} (eq : t ≡ u) → EQREL Γ σ (reflect^βξη σ t) (reflect^βξη σ u)
  reflect^EQREL `Unit     eq = tt
  reflect^EQREL `Bool     eq = cong `embed eq
  reflect^EQREL (σ `→ τ)  eq = λ inc rel → reflect^EQREL τ $ cong₂ _`$_ (cong (wk^ne inc) eq) (reify^EQREL σ rel)

infix 5 _R[_]_
_R[_]_ : {ℓᴬ ℓᴮ ℓᴿ : Level} {A : Con → ty → Set ℓᴬ} {B : Con → ty → Set ℓᴮ}
         {Δ Γ : Con} (as : Δ [ A ] Γ)
         (R : (Γ : Con) (σ : ty) (a : A Γ σ) (b : B Γ σ) → Set ℓᴿ) →
         (bs : Δ [ B ] Γ) → Set ℓᴿ
_R[_]_ {Δ = Δ} {Γ = Γ} as R bs = (σ : ty) (pr : σ ∈ Γ) → R _ σ (as σ pr) (bs σ pr)

wkR[_,_,_] :
  {ℓᴬ ℓᴮ ℓᴿ : Level}
  {A : Con → ty → Set ℓᴬ} (wkA : {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) (a : A Γ σ) → A Δ σ)
  {B : Con → ty → Set ℓᴮ} (wkB : {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) (b : B Γ σ) → B Δ σ)
  {R : (Γ : Con) (σ : ty) (a : A Γ σ) (b : B Γ σ) → Set ℓᴿ} →
  (wkR : {Γ Δ : Con} {σ : ty} {a : A Γ σ} {b : B Γ σ} (inc : Γ ⊆ Δ) (r : R Γ σ a b) →
         R Δ σ (wkA inc a) (wkB inc b)) →
  {Γ Δ Θ : Con} (inc : Δ ⊆ Θ) {as : Δ [ A ] Γ} {bs : Δ [ B ] Γ}
  (ρ : as R[ R ] bs) →  wk[ wkA ] inc as R[ R ] wk[ wkB ] inc bs
wkR[ wkA , wkB , wkR ] = {!!}


-- we should be able to get this from instantiating another
-- thing...
refl^EQREL :
  {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ)
  {ρ₁ ρ₂ : Δ [ _⊨^βξη_ ] Γ} (ρ : ρ₁ R[ EQREL ] ρ₂) →
  EQREL Δ σ (Normalize^βξη ⊨⟦ t ⟧ ρ₁) (Normalize^βξη ⊨⟦ t ⟧ ρ₂)
refl^EQREL (`var v)       ρ = ρ _ v
refl^EQREL (f `$ t)       ρ = refl^EQREL f ρ refl (refl^EQREL t ρ)
refl^EQREL (`λ t)         ρ = λ inc rvw → refl^EQREL t (wkR[ {!!} , {!!} , {!!} ] inc {!!} )
refl^EQREL `⟨⟩            ρ = tt
refl^EQREL `tt            ρ = trivial
refl^EQREL `ff            ρ = trivial
refl^EQREL (`ifte b l r)  ρ = {!!}

module NormalisationFusion =
  Fusion Normalize^βξη Normalize^βξη Normalize^βξη (EQREL _ _) (erase-⊢^nf ∘ reify^βξη _)
         (λ ρB ρA σ pr → Normalize^βξη ⊨⟦ erase-⊢^nf (reify^βξη σ $ ρA σ pr) ⟧ ρB)
         (λ v ρA ρB → refl^EQREL (erase-⊢^nf (reify^βξη _ $ ρA _ v)) {!!}) {!!}
         (λ _ _ → tt) (λ _ _ → trivial) (λ _ _ → trivial)
         (λ _ _ _ _ _ eqb eql eqr → {!!})
         
module NormalisationSubstitutionFusion =
  Fusion Substitution Normalize^βξη Normalize^βξη (EQREL _ _)
         id (λ ρB ρA σ pr → Normalize^βξη ⊨⟦ ρA σ pr ⟧ ρB) (λ v ρA ρB → {!!}) {!!}
--         id (λ ρB ρA σ pr → Normalize^βξη ⊨⟦ ρA σ pr ⟧ ρB) (λ _ _ _ → trivial)
  --       (λ _ _ _ _ eqf eqt → {!!})
    --     (λ _ _ → trivial) (λ _ _ → trivial) (λ _ _ → trivial)
      --   (λ _ _ _ _ _ eqb eql eqr → {!!})

         
\end{code}
