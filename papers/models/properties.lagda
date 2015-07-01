\section{Properties of these \AR{Semantics}}

\begin{code}
module properties where

open import Level
open import Data.Unit
open import Data.Product
open import Function
open import models

record Properties
       {ℓᴱᴬ ℓᴹᴬ : Level} (semA : Semantics ℓᴱᴬ ℓᴹᴬ)
       {ℓᴱᴮ ℓᴹᴮ : Level} (semB : Semantics ℓᴱᴮ ℓᴹᴮ)
       (ℓᴿᴱ ℓᴿᴹ : Level) :
       Set (suc (ℓᴿᴱ ⊔ ℓᴿᴹ) ⊔ ℓᴱᴬ ⊔ ℓᴱᴮ ⊔ ℓᴹᴬ ⊔ ℓᴹᴮ) where
  infixl 5 _R⟦$⟧_
  module SemA = Semantics semA
  module SemB = Semantics semB
  field
    -- environment values
    REnv    : (Γ : Con) (σ : ty) (eA : SemA.Env Γ σ) (eB : SemB.Env Γ σ) → Set ℓᴿᴱ
    Rwk     : {Γ Δ : Con} {σ : ty} {eA : SemA.Env Γ σ} {eB : SemB.Env Γ σ} (inc : Γ ⊆ Δ)
              (r : REnv Γ σ eA eB) → REnv Δ σ (SemA.wk inc eA) (SemB.wk inc eB)
    Rembed  : {Γ : Con} {σ : ty} (pr : σ ∈ Γ) → REnv Γ σ (SemA.embed pr) (SemB.embed pr)
    -- model values
    RMod    : (Γ : Con) (σ : ty) (mA : SemA.Mod Γ σ) (mB : SemB.Mod Γ σ) → Set ℓᴿᴹ
    R⟦var⟧  : {Γ : Con} {σ : ty} {eA : SemA.Env Γ σ} {eB : SemB.Env Γ σ}
              (r : REnv Γ σ eA eB) → RMod Γ σ (SemA.⟦var⟧ eA) (SemB.⟦var⟧ eB)
    _R⟦$⟧_  : {Γ : Con} {σ τ : ty} {fA : SemA.Mod Γ (σ `→ τ)} {fB : SemB.Mod Γ (σ `→ τ)}
              {tA : SemA.Mod Γ σ} {tB : SemB.Mod Γ σ}
              (rf : RMod Γ (σ `→ τ) fA fB) (rt : RMod Γ σ tA tB) → RMod Γ τ (fA SemA.⟦$⟧ tA) (fB SemB.⟦$⟧ tB)
    R⟦λ⟧    : {Γ : Con} {σ τ : ty}
              {tA : {Δ : Con} (pr : Γ ⊆ Δ) (u : SemA.Env Δ σ) → SemA.Mod Δ τ}
              {tB : {Δ : Con} (pr : Γ ⊆ Δ) (u : SemB.Env Δ σ) → SemB.Mod Δ τ} →
              (t : {Δ : Con} (pr : Γ ⊆ Δ) {uA : SemA.Env Δ σ} {uB : SemB.Env Δ σ} (u : REnv Δ σ uA uB) →
                   RMod Δ τ (tA pr uA) (tB pr uB)) →
              RMod Γ (σ `→ τ) (SemA.⟦λ⟧ tA) (SemB.⟦λ⟧ tB)
    R⟦⟨⟩⟧   : {Γ : Con} → RMod Γ `Unit SemA.⟦⟨⟩⟧ SemB.⟦⟨⟩⟧
    R⟦tt⟧   : {Γ : Con} → RMod Γ `Bool SemA.⟦tt⟧ SemB.⟦tt⟧
    R⟦ff⟧   : {Γ : Con} → RMod Γ `Bool SemA.⟦ff⟧ SemB.⟦ff⟧
    R⟦ifte⟧ : {Γ : Con} {bA : SemA.Mod Γ `Bool} {bB : SemB.Mod Γ `Bool} (b : RMod Γ `Bool bA bB) →
              {σ : ty} {lA : SemA.Mod Γ σ} {lB : SemB.Mod Γ σ} (l : RMod Γ σ lA lB) →
              {rA : SemA.Mod Γ σ} {rB : SemB.Mod Γ σ} (r : RMod Γ σ rA rB) →
              RMod Γ σ (SemA.⟦ifte⟧ bA lA rA) (SemB.⟦ifte⟧ bB lB rB)

infix 5 _R[_]_
_R[_]_ : {ℓᴬ ℓᴮ ℓᴿ : Level} {A : Con → ty → Set ℓᴬ} {B : Con → ty → Set ℓᴮ}
         {Δ Γ : Con} (as : Δ [ A ] Γ)
         (R : (Γ : Con) (σ : ty) (a : A Γ σ) (b : B Γ σ) → Set ℓᴿ) →
         (bs : Δ [ B ] Γ) → Set ℓᴿ
_R[_]_ {Γ = ε}     as       R bs       = Lift ⊤
_R[_]_ {Γ = Γ ∙ σ} (as , a) R (bs , b) = as R[ R ] bs × R _ σ a b

wkR[_,_,_] :
  {ℓᴬ ℓᴮ ℓᴿ : Level}
  {A : Con → ty → Set ℓᴬ} (wkA : {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) (a : A Γ σ) → A Δ σ)
  {B : Con → ty → Set ℓᴮ} (wkB : {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) (b : B Γ σ) → B Δ σ)
  {R : (Γ : Con) (σ : ty) (a : A Γ σ) (b : B Γ σ) → Set ℓᴿ} →
  (wkR : {Γ Δ : Con} {σ : ty} {a : A Γ σ} {b : B Γ σ} (inc : Γ ⊆ Δ) (r : R Γ σ a b) →
         R Δ σ (wkA inc a) (wkB inc b)) →
  {Γ Δ Θ : Con} (inc : Δ ⊆ Θ) {as : Δ [ A ] Γ} {bs : Δ [ B ] Γ}
  (ρ : as R[ R ] bs) →  wk[ wkA ] inc as R[ R ] wk[ wkB ] inc bs
wkR[ wkA , wkB , wkR ] {ε}     inc ρ       = lift tt
wkR[ wkA , wkB , wkR ] {Γ ∙ σ} inc (ρ , r) = wkR[ wkA , wkB , wkR ] inc ρ , wkR inc r

_R‼_ : {ℓᴬ ℓᴮ ℓᴿ : Level} {A : Con → ty → Set ℓᴬ} {B : Con → ty → Set ℓᴮ}
       {R : (Γ : Con) (σ : ty) (a : A Γ σ) (b : B Γ σ) → Set ℓᴿ} →
       {Γ Δ : Con} {as : Δ [ A ] Γ} {bs : Δ [ B ] Γ} →
       (rs : as R[ R ] bs) {σ : ty} (pr : σ ∈ Γ) → R Δ σ (as ‼ pr) (bs ‼ pr)
(_  , r) R‼ here!    = r
(rs , _) R‼ there pr = rs R‼ pr

lemma :
  {ℓᴱᴬ ℓᴹᴬ : Level} (semA : Semantics ℓᴱᴬ ℓᴹᴬ)
  {ℓᴱᴮ ℓᴹᴮ : Level} (semB : Semantics ℓᴱᴮ ℓᴹᴮ)
  {ℓᴿᴱ ℓᴿᴹ : Level} (prop : Properties semA semB ℓᴿᴱ ℓᴿᴹ) →
  let open Properties prop
  in {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρA : Δ [ SemA.Env ] Γ} {ρB : Δ [ SemB.Env ] Γ}
     (ρR : ρA R[ REnv ] ρB) → RMod Δ σ (semA ⊨⟦ t ⟧ ρA) (semB ⊨⟦ t ⟧ ρB)
lemma semA semB prop = λ {Γ} → go {Γ} where
  open Properties prop
  go : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρA : Δ [ SemA.Env ] Γ} {ρB : Δ [ SemB.Env ] Γ}
       (ρR : ρA R[ REnv ] ρB) → RMod Δ σ (semA ⊨⟦ t ⟧ ρA) (semB ⊨⟦ t ⟧ ρB)
  go (`var v)      ρR = R⟦var⟧ (ρR R‼ v)
  go (f `$ t)      ρR = go f ρR R⟦$⟧ go t ρR
  go (`λ t)        ρR = R⟦λ⟧ λ inc u → go t (wkR[ SemA.wk , SemB.wk , Rwk ] inc ρR , u) --
  go `⟨⟩           ρR = R⟦⟨⟩⟧
  go `tt           ρR = R⟦tt⟧
  go `ff           ρR = R⟦ff⟧
  go (`ifte b l r) ρR = R⟦ifte⟧ (go b ρR) (go l ρR) (go r ρR)


open import Relation.Binary.PropositionalEquality
            hiding ([_])
            renaming (refl to trivial)

RenamingSubstitution : Properties Renaming Substitution zero zero
RenamingSubstitution =
  record
    { REnv    = λ _ _ pr t → `var pr ≡ t
    ; Rwk     = λ {Γ} {Δ} {σ} {eA} inc eq → subst (λ t → `var (inc ‼ eA) ≡ Renaming ⊨⟦ t ⟧ inc) eq trivial
    ; Rembed  = λ _ → trivial
    ; RMod    = λ _ _ → _≡_
    ; R⟦var⟧  = id
    ; _R⟦$⟧_  = cong₂ _`$_
    ; R⟦λ⟧    = λ t → cong `λ (t (step refl) trivial)
    ; R⟦⟨⟩⟧   = trivial
    ; R⟦tt⟧   = trivial
    ; R⟦ff⟧   = trivial
    ; R⟦ifte⟧ = λ eqb eql → cong₂ (uncurry `ifte) (cong₂ _,_ eqb eql)
    }

renSubst : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρA : Δ [ flip _∈_ ] Γ} {ρB : Δ [ _⊢_ ] Γ}
           (ρR : ρA R[ (λ _ _ v t → `var v ≡ t) ] ρB) →
           Renaming ⊨⟦ t ⟧ ρA ≡ Substitution ⊨⟦ t ⟧ ρB
renSubst = lemma Renaming Substitution RenamingSubstitution


-- Another example:

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

infix 5 _⊢_∋_⟶⋆_
data _⊢_∋_⟶⋆_ (Γ : Con) : (σ : ty) (t : Γ ⊢ σ) (u : Γ ⊢^nf σ) → Set where
  -- already nf
  nf-`tt : Γ ⊢ `Bool ∋ `tt ⟶⋆ `tt
  nf-`ff : Γ ⊢ `Bool ∋ `ff ⟶⋆ `ff
  -- beta reduction
  beta-`λ : {σ τ : ty} {f : Γ ⊢ σ `→ τ} {t : Γ ⊢ σ} {b : Γ ∙ σ ⊢^nf τ} {v : Γ ⊢^nf σ} {w : Γ ⊢^nf τ} →
            Γ ⊢ σ `→ τ ∋ f ⟶⋆ `λ b → Γ ⊢ σ ∋ t ⟶⋆ v →
            Γ ⊢ τ ∋ erase-⊢^nf b ⟨ erase-⊢^nf v /var‿0⟩ ⟶⋆ w →
            Γ ⊢ τ ∋ f `$ t ⟶⋆ w
  beta-`ifte₁ : {σ : ty} {b : Γ ⊢ `Bool} {l r : Γ ⊢ σ} {u : Γ ⊢^nf σ} →
                Γ ⊢ `Bool ∋ b ⟶⋆ `tt → Γ ⊢ σ ∋ l ⟶⋆ u → Γ ⊢ σ ∋ `ifte b l r ⟶⋆ u
  beta-`ifte₂ : {σ : ty} {b : Γ ⊢ `Bool} {l r : Γ ⊢ σ} {u : Γ ⊢^nf σ} →
                Γ ⊢ `Bool ∋ b ⟶⋆ `ff → Γ ⊢ σ ∋ r ⟶⋆ u → Γ ⊢ σ ∋ `ifte b l r ⟶⋆ u
  -- eta expansion
  eta-`⟨⟩ : {t : Γ ⊢ `Unit} → Γ ⊢ `Unit ∋ t ⟶⋆ `⟨⟩
  eta-`λ  : {σ τ : ty} {t : Γ ⊢ σ `→ τ} {b : Γ ∙ σ ⊢^nf τ} → Γ ∙ σ ⊢ τ ∋ wk^⊢ (step refl) t `$ var‿0 ⟶⋆ b →
            Γ ⊢ σ `→ τ ∋ t ⟶⋆ `λ b
-- congruence
  cong-`λ : {σ τ : ty} {t : Γ ∙ σ ⊢ τ} {u : Γ ∙ σ ⊢^nf τ}
            (r : Γ ∙ σ ⊢ τ ∋ t ⟶⋆ u) → Γ ⊢ σ `→ τ ∋ `λ t ⟶⋆ `λ u

reifyReflect : {Γ : Con} (σ : ty) (t : Γ ⊢^ne σ) → Γ ⊢ σ ∋ erase-⊢^ne t ⟶⋆ reify^βξη σ (reflect^βξη σ t)
reifyReflect `Unit    t = eta-`⟨⟩
reifyReflect `Bool    t = {!!}
reifyReflect (σ `→ τ) t = eta-`λ {!!}

SubstitutionNormalize^βξη : Properties Substitution Normalize^βξη zero zero
SubstitutionNormalize^βξη =
  record
    { REnv    = λ Γ σ t v → Γ ⊢ σ ∋ t ⟶⋆ reify^βξη σ v
    ; Rwk     = λ {Γ} {Δ} {σ} {eA} inc r → {!!}
    ; Rembed  = {!!}
    ; RMod    = λ Γ σ t v → Γ ⊢ σ ∋ t ⟶⋆ reify^βξη σ v
    ; R⟦var⟧  = id
    ; _R⟦$⟧_  = λ rf rt → beta-`λ rf rt {!!}
    ; R⟦λ⟧    = λ t → cong-`λ (t (step refl) {!!})
    ; R⟦⟨⟩⟧   = eta-`⟨⟩
    ; R⟦tt⟧   = nf-`tt
    ; R⟦ff⟧   = nf-`ff
    ; R⟦ifte⟧ =
        λ {Γ} {bA} {bB} rb {σ} rl rr →
        (case bB return (λ b → Γ ⊢ `Bool ∋ _ ⟶⋆ b → Γ ⊢ σ ∋ `ifte bA _ _ ⟶⋆ reify^βξη σ (ifte^βξη b _ _)) of λ
          { `tt         r → beta-`ifte₁ r rl
          ; `ff         r → beta-`ifte₂ r rr
          ; (`embed ne) r → {!!} }) rb
    }

substNorm : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρA : Δ [ _⊢_ ] Γ} {ρB : Δ [ _⊨^βξη_ ] Γ}
            (ρR : ρA R[ (λ Γ σ t v → Γ ⊢ σ ∋ t ⟶⋆ reify^βξη σ v) ] ρB) →
            Δ ⊢ σ ∋ Substitution ⊨⟦ t ⟧ ρA ⟶⋆ reify^βξη σ (Normalize^βξη ⊨⟦ t ⟧ ρB)
substNorm = lemma Substitution Normalize^βξη SubstitutionNormalize^βξη 

\end{code}
