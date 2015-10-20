\documentclass[xetex, mathserif, serif]{beamer}
\usepackage[utf8]{inputenc}
\usepackage[english]{babel}
\usepackage[references]{agda}
\setmainfont[Ligatures=TeX]{XITS}
\setmathfont{XITS Math}
\usepackage{newunicodechar}
\usepackage{amssymb}

\begin{code}
module usual where

open import models hiding (Semantics ; Renaming ; Substitution ; Printing ; Normalise^βιξη)
open import Data.Unit
open import Data.Bool
open import Function

ren⟦var⟧ : {Γ : Con} {σ : ty} (pr : σ ∈ Γ) → Γ ⊢ σ
ren⟦var⟧ = `var
ren𝓔 : (Γ : Con) (σ : ty) → Set
ren𝓔 = flip _∈_
sub𝓔 : (Γ : Con) (σ : ty) → Set
sub𝓔 = _⊢_

renextend : {Γ Δ : Con} {σ : ty} (ρ : Δ [ ren𝓔 ] Γ) → Δ ∙ σ [ ren𝓔 ] Γ ∙ σ
renextend = pop!

\end{code}
%<*rename>
\begin{code}
ren : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ ren𝓔 ] Γ) → Δ ⊢ σ
ren (`var v)       ρ = ren⟦var⟧ (ρ _ v)
ren (t `$ u)       ρ = ren t ρ `$ ren u ρ
ren (`λ t)         ρ = `λ (ren t (renextend ρ))
ren `⟨⟩            ρ = `⟨⟩
ren `tt            ρ = `tt
ren `ff            ρ = `ff
ren (`ifte b l r)  ρ = `ifte (ren b ρ) (ren l ρ) (ren r ρ)
\end{code}
%</rename>
\begin{code}
subextend : {Γ Δ : Con} {σ : ty} (ρ : Δ [ _⊢_ ] Γ) → Δ ∙ σ [ _⊢_ ] Γ ∙ σ
subextend ρ = [ _⊢_ ] (λ σ pr → ren (ρ σ pr) (step refl)) `∙ `var zero

sub⟦var⟧ = id
\end{code}
%<*subst>
\begin{code}
sub : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ sub𝓔 ] Γ) → Δ ⊢ σ
sub (`var v)       ρ = sub⟦var⟧ (ρ _ v)
sub (t `$ u)       ρ = sub t ρ `$ sub u ρ
sub (`λ t)         ρ = `λ (sub t (subextend ρ))
sub `⟨⟩            ρ = `⟨⟩
sub `tt            ρ = `tt
sub `ff            ρ = `ff
sub (`ifte b l r)  ρ = `ifte (sub b ρ) (sub l ρ) (sub r ρ)
\end{code}
%</subst>

%<*synextend>
\begin{code}
synextend : {Γ Δ : Con} {σ : ty} {𝓔 : (Γ : Con) (σ : ty) → Set} (𝓢 : Syntactic 𝓔) (ρ : Δ [ 𝓔 ] Γ) → Δ ∙ σ [ 𝓔 ] Γ ∙ σ
synextend {𝓔 = 𝓔} 𝓢 ρ = [ 𝓔 ] ρ′ `∙ var
  where  var  = Syntactic.embed 𝓢 _ zero
         ρ′   = λ σ → Syntactic.wk 𝓢 (step refl) ∘ ρ σ
\end{code}
%</synextend>


%<*syn>
\begin{code}
syn : {Γ Δ : Con} {σ : ty} {𝓔 : (Γ : Con) (σ : ty) → Set} (𝓢 : Syntactic 𝓔) (t : Γ ⊢ σ) (ρ : Δ [ 𝓔 ] Γ) → Δ ⊢ σ
syn 𝓢 (`var v)       ρ = Syntactic.⟦var⟧ 𝓢 (ρ _ v)
syn 𝓢 (t `$ u)       ρ = syn 𝓢 t ρ `$ syn 𝓢 u ρ
syn 𝓢 (`λ t)         ρ = `λ (syn 𝓢 t (synextend 𝓢 ρ))
syn 𝓢 `⟨⟩            ρ = `⟨⟩
syn 𝓢 `tt            ρ = `tt
syn 𝓢 `ff            ρ = `ff
syn 𝓢 (`ifte b l r)  ρ = `ifte (syn 𝓢 b ρ) (syn 𝓢 l ρ) (syn 𝓢 r ρ)
\end{code}
%</syn>

\begin{code}
sem⟦var⟧ = id

semλ : {Γ Δ Θ : Con} {σ τ : ty} (⟦t⟧ : Θ [ _⊨^βιξη_ ] Γ ∙ σ → Θ ⊨^βιξη τ)
       (ρ : Δ ⊆ Θ → Θ ⊨^βιξη σ → Θ [ _⊨^βιξη_ ] Γ ∙ σ) (inc : Δ ⊆ Θ) (u : Θ ⊨^βιξη σ) → Θ ⊨^βιξη τ
semλ ⟦t⟧ ρ inc u = ⟦t⟧ (ρ inc u)

⟨⟩ = tt

semextend : {Γ Δ Θ : Con} {σ : ty} (ρ : Δ [ _⊨^βιξη_ ] Γ) → Δ ⊆ Θ → Θ ⊨^βιξη σ → Θ [ _⊨^βιξη_ ] Γ ∙ σ
semextend ρ inc u = [ _⊨^βιξη_ ] (λ σ → wk^βιξη σ inc ∘ ρ σ) `∙ u
\end{code}

%<*sem>
\begin{code}
sem : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊨^βιξη_ ] Γ) → Δ ⊨^βιξη σ
sem (`var v)       ρ = sem⟦var⟧ (ρ _ v)
sem (t `$ u)       ρ = sem t ρ $^βιξη sem u ρ
sem (`λ t)         ρ = semλ (sem t) (semextend ρ)
sem `⟨⟩            ρ = ⟨⟩
sem `tt            ρ = `tt
sem `ff            ρ = `ff
sem (`ifte b l r)  ρ = ifte^βιξη (sem b ρ) (sem l ρ) (sem r ρ)
\end{code}
%</sem>

%<*semantics>
\begin{code}
record Semantics (𝓔 𝓜 : Con → ty → Set) : Set where
  field 
\end{code}
\uncover<2->{
\begin{code}
    wk      :  {Γ Δ : Con} {σ : ty} → Γ ⊆ Δ → 𝓔 Γ σ → 𝓔 Δ σ
    embed   :  {Γ : Con} → ∀ σ → σ ∈ Γ → 𝓔 Γ σ
    ⟦var⟧   :  {Γ : Con} {σ : ty} → 𝓔 Γ σ → 𝓜 Γ σ
\end{code}}
\uncover<3->{
\begin{code}
    ⟦λ⟧     :  {Γ : Con} {σ τ : ty} → (t : ∀ Δ → Γ ⊆ Δ → 𝓔 Δ σ → 𝓜 Δ τ) → 𝓜 Γ (σ `→ τ)
\end{code}}
\uncover<4->{
\begin{code}
    _⟦$⟧_   :  {Γ : Con} {σ τ : ty} → 𝓜 Γ (σ `→ τ) → 𝓜 Γ σ → 𝓜 Γ τ
\end{code}}
\uncover<5->{
\begin{code}
    ⟦⟨⟩⟧    :  {Γ : Con} → 𝓜 Γ `Unit
    ⟦tt⟧    :  {Γ : Con} → 𝓜 Γ `Bool
    ⟦ff⟧    :  {Γ : Con} → 𝓜 Γ `Bool
    ⟦ifte⟧  :  {Γ : Con} {σ : ty} (b : 𝓜 Γ `Bool) (l r : 𝓜 Γ σ) → 𝓜 Γ σ
\end{code}}
%</semantics>

%<*semexamples>
\begin{code}
Renaming        : models.Semantics (flip _∈_) _⊢_
Substitution    : models.Semantics _⊢_ _⊢_
Printing        : models.Semantics Name Printer
Normalise^βιξη  : models.Semantics _⊨^βιξη_ _⊨^βιξη_
\end{code}
%</semexamples>

\begin{code}
Renaming = syntactic syntacticRenaming
Substitution = syntactic syntacticSubstitution
Printing = models.Printing
Normalise^βιξη = models.Normalise^βιξη
\end{code}
