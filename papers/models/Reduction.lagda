\begin{code}
module Reduction where

open import models
open import Data.Unit
open import Function hiding (_⟨_⟩_)
import Relation.Binary.PropositionalEquality as PEq

infix 1 _⟶_
data _⟶_ {Γ : Con} : {σ : ty} (t u : Γ ⊢ σ) → Set where
  `λβ     : {σ τ : ty} (b : (Γ ∙ σ) ⊢ τ) (u : Γ ⊢ σ) → (`λ b) `$ u ⟶ b ⟨ u /var₀⟩
  `ifteι₁ : {σ : ty} (l r : Γ ⊢ σ)       → `ifte `tt l r ⟶ l
  `ifteι₂ : {σ : ty} (l r : Γ ⊢ σ)       → `ifte `ff l r ⟶ r
  `⟨⟩η    : (t : Γ ⊢ `Unit)              → t             ⟶ `⟨⟩
  `λη     : {σ τ : ty} (t : Γ ⊢ σ `→ τ)  → t             ⟶ `λ (wk^⊢ (step refl) t `$ `var zero)

wk^⟶ : {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) → {t u : Γ ⊢ σ} → t ⟶ u → wk^⊢ inc t ⟶ wk^⊢ inc u
wk^⟶ inc (`λβ b u)      = PEq.subst (wk^⊢ inc (`λ b `$ u) ⟶_) {!!}
                         $′ `λβ (wk^⊢ (pop! inc) b) (wk^⊢ inc u)
wk^⟶ inc (`ifteι₁ l r)  = `ifteι₁ (wk^⊢ inc l) (wk^⊢ inc r)
wk^⟶ inc (`ifteι₂ l r)  = `ifteι₂ (wk^⊢ inc l) (wk^⊢ inc r)
wk^⟶ inc (`⟨⟩η t)       = `⟨⟩η (wk^⊢ inc t)
wk^⟶ inc (`λη t)        = PEq.subst (wk^⊢ inc t ⟶_) (PEq.cong (λ b → `λ (b `$ `var zero)) {!!})
                         $′ `λη (wk^⊢ inc t)

Rel : Set → Set₁
Rel A = A → A → Set

data [_]⟨_⟩⟨_⟩ (R : {Γ : Con} {σ : ty} → Rel (Γ ⊢ σ)) {Γ : Con} : {σ : ty} → Rel (Γ ⊢ σ) where
  ⟨_⟩   : {σ : ty} {t u : Γ ⊢ σ} → R t u → [ R ]⟨ t ⟩⟨ u ⟩
  _`$_  : {σ τ : ty} {f g : Γ ⊢ (σ `→ τ)} → [ R ]⟨ f ⟩⟨ g ⟩ → {t u : Γ ⊢ σ} → [ R ]⟨ t ⟩⟨ u ⟩ →
          [ R ]⟨ f `$ t ⟩⟨ g `$ u ⟩
  `λ    : {σ τ : ty} {f g : (Γ ∙ σ) ⊢ τ} → [ R ]⟨ f ⟩⟨ g ⟩ → [ R ]⟨ `λ f ⟩⟨ `λ g ⟩
  `ifte : {σ : ty} {b c : Γ ⊢ `Bool} → [ R ]⟨ b ⟩⟨ c ⟩ → {l m r s : Γ ⊢ σ} →
          [ R ]⟨ l ⟩⟨ m ⟩ → [ R ]⟨ r ⟩⟨ s ⟩ → [ R ]⟨ `ifte b l r ⟩⟨ `ifte c m s ⟩

data [_]? {A : Set} (R : Rel A) : Rel A where
  none : {a : A}           → [ R ]? a a
  some : {a b : A} → R a b → [ R ]? a b

data [_]* {A : Set} (R : Rel A) : Rel A where
  none : {a : A}                          → [ R ]* a a
  some : {a b c : A} → R a b → [ R ]* b c → [ R ]* a c

map : {A B : Set} {R : Rel A} {S : Rel B} {a b : A}
      (f : A → B) (prf : {a b : A} → R a b → S (f a) (f b)) →
      [ R ]* a b → [ S ]* (f a) (f b)
map f prf none        = none
map f prf (some r pr) = some (prf r) (map f prf pr)

somes : {A : Set} {R : Rel A} {a b c : A} → [ R ]* a b → [ R ]* b c → [ R ]* a c
somes none        qs = qs
somes (some r pr) qs = some r (somes pr qs)

infix 1 _⇒*_
_⇒*_ : {Γ : Con} {σ : ty} → Rel (Γ ⊢ σ)
_⇒*_ = [ [ [ _⟶_ ]? ]⟨_⟩⟨_⟩ ]*


private

  open import Function using (_∋_ ; _$_)

  example : `ifte `tt (`λ (`var zero) `$ `ff) `tt ⇒* (ε ⊢ `Bool ∋ `ff)
  example =
    let step₁ : `λ (`var zero) `$ `ff ⟶ `var zero ⟨ `ff /var₀⟩
        step₁ = `λβ (`var zero) `ff

        step₂ : `ifte `tt `ff `tt ⟶ `ff
        step₂ = `ifteι₁ `ff `tt
    in some (`ifte ⟨ none ⟩ ⟨ some step₁ ⟩ ⟨ none ⟩)
    $′ some ⟨ some step₂ ⟩
       none

mutual

  erase^nf : {Γ : Con} {σ : ty} {R : ty → Set} → Γ ⊢[ R ]^nf σ → Γ ⊢ σ
  erase^nf (`embed pr ne) = erase^ne ne
  erase^nf `⟨⟩            = `⟨⟩
  erase^nf `tt            = `tt
  erase^nf `ff            = `ff
  erase^nf (`λ nf)        = `λ (erase^nf nf)
  
  erase^ne : {Γ : Con} {σ : ty} {R : ty → Set} → Γ ⊢[ R ]^ne σ → Γ ⊢ σ
  erase^ne (`var v)       = `var v
  erase^ne (ne `$ u)      = erase^ne ne `$ erase^nf u
  erase^ne (`ifte ne l r) = `ifte (erase^ne ne) (erase^nf l) (erase^nf r)

mutual

  erase-wk^nf : {Γ Δ : Con} {σ : ty} {R : ty → Set} (inc : Γ ⊆ Δ) (nf : Γ ⊢[ R ]^nf σ) →
                erase^nf (wk^nf inc nf) PEq.≡ wk^⊢ inc (erase^nf nf)
  erase-wk^nf inc (`embed pr t)  = erase-wk^ne inc t
  erase-wk^nf inc `⟨⟩            = PEq.refl
  erase-wk^nf inc `tt            = PEq.refl
  erase-wk^nf inc `ff            = PEq.refl
  erase-wk^nf inc (`λ nf)        = PEq.cong `λ (erase-wk^nf (pop! inc) nf)
  
  erase-wk^ne : {Γ Δ : Con} {σ : ty} {R : ty → Set} (inc : Γ ⊆ Δ) (ne : Γ ⊢[ R ]^ne σ) →
                erase^ne (wk^ne inc ne) PEq.≡ wk^⊢ inc (erase^ne ne)
  erase-wk^ne inc (`var v)        = PEq.refl
  erase-wk^ne inc (ne `$ u)       = PEq.cong₂ _`$_ (erase-wk^ne inc ne) (erase-wk^nf inc u)
  erase-wk^ne inc (`ifte ne l r)
    rewrite erase-wk^ne inc ne = PEq.cong₂ (`ifte _) (erase-wk^nf inc l) (erase-wk^nf inc r)

_reducesTo_ : {Γ : Con} {σ : ty} → Γ ⊢ σ → Γ ⊨^βιξη σ → Set
t reducesTo T = t ⇒* erase^nf (reify^βιξη _ T)

[_]_⇊_ : {Γ : Con} (σ : ty) → Γ ⊢ σ → Γ ⊨^βιξη σ → Set
[ `Unit   ] t ⇊ T = ⊤
[ `Bool   ] t ⇊ T = t reducesTo T
[ σ `→ τ  ] t ⇊ T = {Δ : Con} (inc : _ ⊆ Δ) {v : Δ ⊢ σ} {V : Δ ⊨^βιξη σ} → [ σ ] v ⇊ V →
                    {tv : Δ ⊢ τ} → tv ⇒* wk^⊢ inc t `$ v → [ τ ] tv ⇊ T inc V

kripke : {Γ : Con} (σ : ty) {s t : Γ ⊢ σ} (T : Γ ⊨^βιξη σ) → s ⇒* t → [ σ ] t ⇊ T → [ σ ] s ⇊ T
kripke `Unit     T pr tT = tt
kripke `Bool     T pr tT = somes pr tT
kripke (σ `→ τ)  T pr tT = λ inc vV qs → tT inc vV $′ somes qs
                                                 $′ map (_`$ _) (_`$ ⟨ none ⟩)
                                                 $′ map (wk^⊢ inc) {!!} pr

mutual

  corollary : {Γ : Con} (σ : ty) {t : Γ ⊢ σ} {T : Γ ⊨^βιξη σ} → [ σ ] t ⇊ T → t reducesTo T
  corollary `Unit     pr = some ⟨ some $′ `⟨⟩η _ ⟩ none
  corollary `Bool     pr = pr
  corollary (σ `→ τ)  pr =  some ⟨ some $′ `λη _ ⟩
                         $′ map `λ `λ $′ corollary τ $′ pr (step refl) (related^ne σ $ `var zero) none

  related^ne : {Γ : Con} (σ : ty) (ne : Γ ⊢[ R^βιξη ]^ne σ) → [ σ ] erase^ne ne ⇊ reflect^βιξη σ ne
  related^ne `Unit     ne = tt
  related^ne `Bool     ne = none
  related^ne (σ `→ τ)  ne = λ inc {_} {V} vV r →
        let NE = reflect^βιξη (σ `→ τ) ne
            v  = reify^βιξη σ V
        in kripke τ (reflect^βιξη τ (wk^ne inc ne `$ v))
           (somes r $′ map (_ `$_) (⟨ none ⟩ `$_) $′ corollary σ vV)
        $′ PEq.subst (λ t → [ τ ] t `$ erase^nf v ⇊ NE inc V) (erase-wk^ne inc ne)
        $′ related^ne τ (wk^ne inc ne `$ v)

NormaliseReduces : Synchronisable Substitution Normalise^βιξη [ _ ]_⇊_ [ _ ]_⇊_
NormaliseReduces = record
  { 𝓔^R‿wk   = {!!}
  ; R⟦var⟧   = λ v ρ^R → ρ^R _ v
  ; R⟦λ⟧     = λ t inc vV r → kripke _ _ (somes r (some ⟨ some (`λβ _ _) ⟩ {!!})) (t inc vV)
  ; R⟦$⟧     = λ f^R u^R → f^R refl u^R {!!}
  ; R⟦⟨⟩⟧    = tt
  ; R⟦tt⟧    = none
  ; R⟦ff⟧    = none
  ; R⟦ifte⟧  = {!!} }
\end{code}
