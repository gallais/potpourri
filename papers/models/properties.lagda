\section{Properties of these \AR{Semantics}}

\begin{code}
module properties where

open import Level
open import Data.Unit
open import Data.Product
open import Function
open import models

record Properties {ℓᴱ ℓᴹ : Level} (sem : Semantics ℓᴱ ℓᴹ) (ℓʳ ℓᴿᴱ ℓᴿᴹ : Level) :
       Set (suc (ℓʳ ⊔ ℓᴿᴱ ⊔ ℓᴿᴹ) ⊔ ℓᴱ ⊔ ℓᴹ) where
  open Semantics sem
  infixl 5 _R⟦$⟧_
  field
    -- reduction relation
    Red    : {Γ : Con} {σ : ty} (t u : Γ ⊢ σ) → Set ℓʳ
    -- environment values
    REnv   : {Γ : Con} {σ : ty} (t : Γ ⊢ σ) (e : Env Γ σ) → Set ℓᴿᴱ
    Rwk    : {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) {t : Γ ⊢ σ} {e : Env Γ σ}
             (r : REnv t e) → REnv (wk^⊢ inc t) (wk inc e)
    Rembed : {Γ : Con} {σ : ty} (pr : σ ∈ Γ) → REnv (`var pr) (embed pr)
    -- model values
    RMod   : {Γ : Con} {σ : ty} (t : Γ ⊢ σ) (m : Mod Γ σ) → Set ℓᴿᴹ
    R⟦var⟧ : {Γ : Con} {σ : ty} {t : Γ ⊢ σ} {e : Env Γ σ} (r : REnv t e) → RMod t (⟦var⟧ e)
    _R⟦$⟧_ : {Γ : Con} {σ τ : ty} {f : Γ ⊢ σ `→ τ} {t : Γ ⊢ σ} {F : Mod Γ (σ `→ τ)} {T : Mod Γ σ}
             (rfF : RMod f F) (rtT : RMod t T) → RMod (f `$ t) (F ⟦$⟧ T)
    R⟦⟨⟩⟧  : {Γ : Con} → RMod {Γ} `⟨⟩ ⟦⟨⟩⟧
    R⟦tt⟧  : {Γ : Con} → RMod {Γ} `tt ⟦tt⟧
    R⟦ff⟧  : {Γ : Con} → RMod {Γ} `ff ⟦ff⟧
    -- normalisation result
    reify  : {Γ : Con} (σ : ty) (m : Mod Γ σ) → Γ ⊢ σ
    norm   : {Γ : Con} {σ : ty} {t : Γ ⊢ σ} {m : Mod Γ σ} → RMod t m → Red t (reify σ m)

infix 5 _R[_]_
_R[_]_ : {ℓᴬ ℓᴮ ℓᴿ : Level} {A : Con → ty → Set ℓᴬ} {B : Con → ty → Set ℓᴮ}
         {Δ Γ : Con} (as : Δ [ A ] Γ)
         (R : {Γ : Con} {σ : ty} (a : A Γ σ) (b : B Γ σ) → Set ℓᴿ) →
         (bs : Δ [ B ] Γ) → Set ℓᴿ
_R[_]_ {Γ = ε}     as       R bs       = Lift ⊤
_R[_]_ {Γ = Γ ∙ σ} (as , a) R (bs , b) = as R[ R ] bs × R a b

_R‼_ : {ℓᴬ ℓᴮ ℓᴿ : Level} {A : Con → ty → Set ℓᴬ} {B : Con → ty → Set ℓᴮ}
       {R : {Γ : Con} {σ : ty} (a : A Γ σ) (b : B Γ σ) → Set ℓᴿ} →
       {Γ Δ : Con} {as : Δ [ A ] Γ} {bs : Δ [ B ] Γ} →
       (rs : as R[ R ] bs) {σ : ty} (pr : σ ∈ Γ) → R (as ‼ pr) (bs ‼ pr)
(_  , r) R‼ here!    = r
(rs , _) R‼ there pr = rs R‼ pr

lemma : {ℓᴱ ℓᴹ ℓʳ ℓᴿᴱ ℓᴿᴹ : Level} (sem : Semantics ℓᴱ ℓᴹ) (prop : Properties sem ℓʳ ℓᴿᴱ ℓᴿᴹ) →
        let open Semantics sem
            open Properties prop in
        {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρe : Δ [ _⊢_ ] Γ} {ρE : Δ [ Env ] Γ}
        (ρR : ρe R[ REnv ] ρE) → RMod (Substitution ⊨⟦ t ⟧ ρe) (sem ⊨⟦ t ⟧ ρE)
lemma sem prop (`var v)      ρR = let open Properties prop in R⟦var⟧ (ρR R‼ v)
lemma sem prop (f `$ t)      ρR = let open Properties prop in lemma sem prop f ρR R⟦$⟧ lemma sem prop t ρR
lemma sem prop (`λ t)        ρR = {!!}
lemma sem prop `⟨⟩           ρR = let open Properties prop in R⟦⟨⟩⟧
lemma sem prop `tt           ρR = let open Properties prop in R⟦tt⟧
lemma sem prop `ff           ρR = let open Properties prop in R⟦ff⟧
lemma sem prop (`ifte b l r) ρR = {!!}

envi : 
  {ℓᴱ ℓᴹ ℓʳ ℓᴿᴱ ℓᴿᴹ : Level} (sem : Semantics ℓᴱ ℓᴹ) (prop : Properties sem ℓʳ ℓᴿᴱ ℓᴿᴹ) →
  let open Semantics sem
      open Properties prop in
  (Γ : Con) → pure {R = _⊢_} {Γ = Γ} (λ _ → `var) R[ REnv ] pure (λ _ → embed)
envi sem prop Γ = go Γ (λ _ → `var) (λ _ → embed) (λ _ → Rembed)
  where
    open Properties prop
    open Semantics sem

    go : {Δ : Con} (Γ : Con) (f : (σ : ty) (pr : σ ∈ Γ) → Δ ⊢ σ) (g : (σ : ty) (pr : σ ∈ Γ) → Env Δ σ)
         (r : (σ : ty) (pr : σ ∈ Γ) → REnv (f σ pr) (g σ pr)) →
         pure {R = _⊢_} {Γ = Γ} f R[ REnv ] pure g
    go ε       f g r = lift tt
    go (Γ ∙ σ) f g r = go Γ (λ σ → f σ ∘ there) (λ σ → g σ ∘ there) (λ σ → r σ ∘ there) , r σ here!

normalisation :
  {ℓᴱ ℓᴹ ℓʳ ℓᴿᴱ ℓᴿᴹ : Level} (sem : Semantics ℓᴱ ℓᴹ) (prop : Properties sem ℓʳ ℓᴿᴱ ℓᴿᴹ) →
  let open Semantics sem
      open Properties prop in
  {Γ : Con} {σ : ty} (t : Γ ⊢ σ) → Red t (reify σ (sem ⊨eval t))
normalisation sem prop t =
  let open Properties prop
      result = norm (lemma sem prop t (envi sem prop _))
  in {!!}
\end{code}

  field
    -- environment values and corresponding methods
    Env     : (Δ : Con) (σ : ty) → Set ℓᴱ
    wk      : {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) (r : Env Γ σ) → Env Δ σ
    embed   : {Γ : Con} {σ : ty} (pr : σ ∈ Γ) → Env Γ σ
    -- model and semantic counterparts of the constructors
    Mod     : (Δ : Con) (σ : ty) → Set ℓᴹ
    ⟦var⟧   : {Γ : Con} {σ : ty} → Env Γ σ → Mod Γ σ
    _⟦$⟧_   : {Γ : Con} {σ τ : ty} → Mod Γ (σ `→ τ) → Mod Γ σ → Mod Γ τ
    ⟦λ⟧     : {Γ : Con} {σ τ : ty} (t : {Δ : Con} (pr : Γ ⊆ Δ) (u : Env Δ σ) → Mod Δ τ) → Mod Γ (σ `→ τ)
    ⟦⟨⟩⟧    : {Γ : Con} → Mod Γ `Unit
    ⟦tt⟧    : {Γ : Con} → Mod Γ `Bool
    ⟦ff⟧    : {Γ : Con} → Mod Γ `Bool
    ⟦ifte⟧  : {Γ : Con} {σ : ty} (b : Mod Γ `Bool) (l r : Mod Γ σ) → Mod Γ σ
