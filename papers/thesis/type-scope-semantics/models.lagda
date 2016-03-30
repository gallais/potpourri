\begin{code}
{-# OPTIONS --copatterns #-}
module models where

open import Level using (Level ; _⊔_)
open import Data.Empty
open import Data.Unit renaming (tt to ⟨⟩)
open import Data.Bool
open import Data.Sum hiding (map ; [_,_])
open import Data.Product hiding (map)
open import Function

infixr 1 _$′_
_$′_ : {A B : Set} (f : A → B) (a : A) → B
_$′_ = _$_

infixr 20 _`→_
infixl 10 _∙_
infix 5 _∈_
infixr 5 1+_
\end{code}
%<*ty>
\begin{code}
data ty : Set where
  `Unit  : ty
  `Bool  : ty
  _`→_   : (σ τ : ty) → ty
\end{code}
%</ty>

%<*context>
\begin{code}
data Con : Set where
  ε    : Con
  _∙_  : Con → ty → Con
\end{code}
%</context>

%<*var>
\begin{code}
data _∈_ (σ : ty) : Con → Set where
  zero  : {Γ : Con} → σ ∈ (Γ ∙ σ)
  1+_   : {Γ : Con} {τ : ty} → σ ∈ Γ → σ ∈ (Γ ∙ τ)
\end{code}
%</var>

\begin{code}
open import Data.Nat as ℕ using (ℕ ; _+_)

size : Con → ℕ
size ε        = 0
size (Γ ∙ _)  = 1 + size Γ

infix 5 _⊢_
infixl 5 _`$_
\end{code}

%<*term>
\begin{code}
data _⊢_ (Γ : Con) : (σ : ty) → Set where
  `var     : {σ : ty} (v : σ ∈ Γ) → Γ ⊢ σ
  _`$_     : {σ τ : ty} (t : Γ ⊢ (σ `→ τ)) (u : Γ ⊢ σ) → Γ ⊢ τ
  `λ       : {σ τ : ty} (t : Γ ∙ σ ⊢ τ) → Γ ⊢ (σ `→ τ)
  `⟨⟩      : Γ ⊢ `Unit
  `tt `ff  : Γ ⊢ `Bool
  `ifte    : {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) → Γ ⊢ σ
\end{code}
%</term>

\begin{code}
infix 5 _[_]_
\end{code}

%<*environment>
\begin{code}
record _[_]_ {ℓ : Level} (Δ : Con) (𝓔 : Con → ty → Set ℓ) (Γ : Con) : Set ℓ where
  constructor pack
  field lookup : {σ : ty} (v : σ ∈ Γ) → 𝓔 Δ σ
\end{code}
%</environment>

\begin{code}
open _[_]_ public

infixl 10 _`∙_
\end{code}

%<*empty-env>
\begin{code}
`ε : {ℓ : Level} {Δ : Con} {𝓔 : (Δ : Con) (σ : ty) → Set ℓ} → Δ [ 𝓔 ] ε
`ε = pack $ λ ()
\end{code}
%</empty-env>

%<*cons-env>
\begin{code}
_`∙_ :  {ℓ : Level} {Γ Δ : Con} {𝓔 : Con → ty → Set ℓ} {σ : ty} → Δ [ 𝓔 ] Γ → 𝓔 Δ σ → Δ [ 𝓔 ] (Γ ∙ σ)
lookup (ρ `∙ s) zero    = s
lookup (ρ `∙ s) (1+ n)  = lookup ρ n
\end{code}

%</cons-env>
\begin{code}

infix 5 _⊆_

\end{code}

%<*inclusion>
\begin{code}
_⊆_ : (Γ Δ : Con) → Set
Γ ⊆ Δ = Δ [ flip _∈_ ] Γ
\end{code}
%</inclusion>

%<*weak-var>
\begin{code}
wk^∈ : {Δ Γ : Con} {σ : ty} → Γ ⊆ Δ → σ ∈ Γ → σ ∈ Δ
wk^∈ inc v = lookup inc v
\end{code}
%</weak-var>

%<*weak-env>
\begin{code}
wk[_] :  {ℓ : Level} {Δ : Con} {𝓔 : (Δ : Con) (σ : ty) → Set ℓ} (wk : {Θ : Con} {σ : ty} (inc : Δ ⊆ Θ) → 𝓔 Δ σ → 𝓔 Θ σ) →
         {Γ Θ : Con} → Δ ⊆ Θ → Δ [ 𝓔 ] Γ →  Θ [ 𝓔 ] Γ
wk[ wk ] inc ρ = pack $ wk inc ∘ lookup ρ
\end{code}
%</weak-env>

%<*inclusion-refl>
\begin{code}
refl : {Γ : Con} → Γ ⊆ Γ
refl = pack id
\end{code}
%</inclusion-refl>

%<*inclusion-trans>
\begin{code}
trans : {l : Level} {Γ Δ Θ : Con} {𝓔 : Con → ty → Set l} → (inc : Γ ⊆ Δ) (ρ : Θ [ 𝓔 ] Δ) → Θ [ 𝓔 ] Γ
lookup (trans inc ρ) = lookup ρ ∘ lookup inc
\end{code}
%</inclusion-trans>
%<*inclusion-steps>
\begin{code}
step : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) → Γ ⊆ (Δ ∙ σ)
step inc = trans inc $ pack 1+_
\end{code}
%</inclusion-step>
%<*inclusion-pop>
\begin{code}
pop! : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) → (Γ ∙ σ) ⊆ (Δ ∙ σ)
pop! inc = step inc `∙ zero
\end{code}
%</inclusion-pop>
%<*semantics-record>
\begin{code}
record Semantics {ℓ^E ℓ^M : Level} (𝓔 : Con → ty → Set ℓ^E) (𝓜 : Con → ty → Set ℓ^M) : Set (ℓ^E ⊔ ℓ^M) where
\end{code}
%</semantics-record>

\begin{code}

  infixl 5 _⟦$⟧_
  field

\end{code}

%<*semantics-wkemb>
\begin{code}
    wk      :  {Γ Δ : Con} {σ : ty} (inc : Γ ⊆ Δ) (r : 𝓔 Γ σ) → 𝓔 Δ σ
    embed   :  {Γ : Con} {σ : ty} (v : σ ∈ Γ) → 𝓔 Γ σ
\end{code}
%</semantics-wkemb>
%<*semantics-var>
\begin{code}
    ⟦var⟧   :  {Γ : Con} {σ : ty} (v : 𝓔 Γ σ) → 𝓜 Γ σ
\end{code}
%</semantics-var>
%<*semantics-kripke>
\begin{code}
  Kripke : Con → ty → ty → Set (ℓ^M ⊔ ℓ^E)
  Kripke Γ σ τ = {Δ : Con} → Γ ⊆ Δ → 𝓔 Δ σ → 𝓜 Δ τ
\end{code}
%</semantics-kripke>
\begin{code}
  field
\end{code}
%<*semantics-lam>
\begin{code}

    ⟦λ⟧     :  {Γ : Con} {σ τ : ty} (t : Kripke Γ σ τ) → 𝓜 Γ (σ `→ τ)
\end{code}
%</semantics-lam>
%<*semantics-rest>
\begin{code}
    _⟦$⟧_   :  {Γ : Con} {σ τ : ty} → 𝓜 Γ (σ `→ τ) → 𝓜 Γ σ → 𝓜 Γ τ
    ⟦⟨⟩⟧    :  {Γ : Con} → 𝓜 Γ `Unit
    ⟦tt⟧    :  {Γ : Con} → 𝓜 Γ `Bool
    ⟦ff⟧    :  {Γ : Con} → 𝓜 Γ `Bool
    ⟦ifte⟧  :  {Γ : Con} {σ : ty} (b : 𝓜 Γ `Bool) (l r : 𝓜 Γ σ) → 𝓜 Γ σ
\end{code}
%</semantics-rest>
%<*evaluation-module>
\begin{code}
module Eval {ℓ^E ℓ^M : Level} {𝓔 : (Γ : Con) (σ : ty) → Set ℓ^E} {𝓜 : (Γ : Con) (σ : ty) → Set ℓ^M} (𝓢 : Semantics 𝓔 𝓜) where
  open Semantics 𝓢
\end{code}
%</evaluation-module>
\begin{code}
  infix 10 _⊨⟦_⟧_ _⊨eval_
\end{code}
%<*evaluation>
\begin{code}
  lemma : {Δ Γ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ 𝓔 ] Γ) → 𝓜 Δ σ
  lemma (`var v)       ρ = ⟦var⟧ $ lookup ρ v
  lemma (t `$ u)       ρ = lemma t ρ ⟦$⟧ lemma u ρ
  lemma (`λ t)         ρ = ⟦λ⟧ λ inc u → lemma t $ wk[ wk ] inc ρ `∙ u
  lemma `⟨⟩            ρ = ⟦⟨⟩⟧
  lemma `tt            ρ = ⟦tt⟧
  lemma `ff            ρ = ⟦ff⟧
  lemma (`ifte b l r)  ρ = ⟦ifte⟧ (lemma b ρ) (lemma l ρ) (lemma r ρ)
\end{code}
%</evaluation>
%<*evaluation-alias>
\begin{code}
  _⊨⟦_⟧_ : {Δ Γ : Con} {σ : ty} → Γ ⊢ σ → Δ [ 𝓔 ] Γ → 𝓜 Δ σ
  _⊨⟦_⟧_ = lemma
\end{code}
%</evaluation-alias>
%<*evaluation-dummy>
\begin{code}
  _⊨eval_ : {Γ : Con} {σ : ty} → Γ ⊢ σ → 𝓜 Γ σ
  _⊨eval_ t = _⊨⟦_⟧_ t (pack embed)
\end{code}
%</evaluation-dummy>
\begin{code}
  _⟨_/0⟩ : {Γ : Con} {σ τ : ty} → (Γ ∙ σ) ⊢ τ → 𝓔 Γ σ → 𝓜 Γ τ
  t ⟨ u /0⟩ = lemma t (pack embed `∙ u)

open Eval hiding (lemma) public

\end{code}
%<*syntactic-record>
\begin{code}
record Syntactic {ℓ : Level} (𝓔 : Con → ty → Set ℓ) : Set ℓ where
  field  embed  : {Γ : Con} {σ : ty} → σ ∈ Γ → 𝓔 Γ σ
         wk     : {Γ Δ : Con} {σ : ty} → Γ ⊆ Δ → 𝓔 Γ σ → 𝓔 Δ σ
         ⟦var⟧  : {Γ : Con} {σ : ty} → 𝓔 Γ σ → Γ ⊢ σ
\end{code}
%</syntactic-record>
%<*syntactic>
\begin{code}
syntactic : {ℓ : Level} {𝓔 : (Γ : Con) (σ : ty) → Set ℓ} (syn : Syntactic 𝓔) → Semantics 𝓔 _⊢_
syntactic syn = let open Syntactic syn in record
  { wk      = wk; embed   = embed; ⟦var⟧   = ⟦var⟧
  ; ⟦λ⟧     = λ t → `λ $ t (step refl) $ embed zero
  ; _⟦$⟧_   = _`$_; ⟦⟨⟩⟧ = `⟨⟩; ⟦tt⟧ = `tt; ⟦ff⟧ = `ff; ⟦ifte⟧  = `ifte }
\end{code}
%</syntactic>
%<*syntactic-renaming>
\begin{code}
syntacticRenaming : Syntactic (flip _∈_)
syntacticRenaming = record { embed = id; wk = wk^∈; ⟦var⟧ = `var }

Renaming : Semantics (flip _∈_) _⊢_; Renaming = syntactic syntacticRenaming
\end{code}
%</syntactic-renaming>
%<*weak-term>
\begin{code}
wk^⊢ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (t : Γ ⊢ σ) → Δ ⊢ σ
wk^⊢ inc t = Renaming ⊨⟦ t ⟧ inc
\end{code}
%</weak-term>
%<*syntactic-substitution>
\begin{code}
syntacticSubstitution : Syntactic _⊢_
syntacticSubstitution = record { embed = `var; wk = wk^⊢; ⟦var⟧ = id }

Substitution : Semantics _⊢_ _⊢_; Substitution = syntactic syntacticSubstitution
\end{code}
%</syntactic-substitution>
%<*subst-term>
\begin{code}
subst : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Δ [ _⊢_ ] Γ) → Δ ⊢ σ
subst t ρ = Substitution ⊨⟦ t ⟧ ρ
\end{code}
%</subst-term>
\begin{code}
open import Data.Char using (Char)
open import Data.String hiding (show)
open import Data.Nat.Show
open import Data.List as List hiding (_++_ ; zipWith ; [_])
open import Coinduction
open import Data.Stream as Stream using (Stream ; head ; tail ; zipWith ; _∷_)
open import Category.Monad
open import Category.Monad.State
open RawIMonadState (StateMonadState (Stream String)) hiding (zipWith ; pure)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

\end{code}
%<*name-record>
\begin{code}
record Name (Γ : Con) (σ : ty) : Set where
  constructor mkName
  field runName : String
\end{code}
%</name-record>
%<*printer-record>
\begin{code}
record Printer (Γ : Con) (σ : ty) : Set where
  constructor mkPrinter
  field runPrinter : State (Stream String) String
\end{code}
%</printer-record>
\begin{code}
open Name
open Printer

formatλ : String → String → String
formatλ x b = "λ" ++ x ++ ". " ++ b

format$ : String → String → String
format$ f t = f ++ " (" ++ t ++ ")"

formatIf : String → String → String → String
formatIf b l r = "if (" ++ b  ++ ") then (" ++ l ++ ") else (" ++ r ++ ")"

\end{code}
%<*printer>
\begin{code}
Printing : Semantics Name Printer
Printing = record
  { embed   = mkName ∘ show ∘ deBruijn
  ; wk      = λ _ → mkName ∘ runName
  ; ⟦var⟧   = mkPrinter ∘ return ∘ runName
  ; _⟦$⟧_   =  λ mf mt → mkPrinter $ format$ <$> runPrinter mf ⊛ runPrinter mt
  ; ⟦λ⟧     =  λ {_} {σ} mb →
               mkPrinter $ get >>= λ names → let `x` = head names in
               put (tail names)                                  >>= λ _ →
               runPrinter (mb (step {σ = σ} refl) (mkName `x`))  >>= λ `b` →
               return $ formatλ `x` `b`
  ; ⟦⟨⟩⟧    = mkPrinter $ return "⟨⟩"
  ; ⟦tt⟧    = mkPrinter $ return "tt"
  ; ⟦ff⟧    = mkPrinter $ return "ff"
  ; ⟦ifte⟧  =  λ mb ml mr → mkPrinter $
               formatIf <$> runPrinter mb ⊛ runPrinter ml ⊛ runPrinter mr }
\end{code}
%</printer>
%<*printer-debruijn>
\begin{code}
  where
    deBruijn : {Γ : Con} {σ : ty} → σ ∈ Γ → ℕ
    deBruijn zero    = 0
    deBruijn (1+ n)  = 1 + deBruijn n
\end{code}
%</printer-debruijn>
\begin{code}
flatten : {A : Set} → Stream (A × List A) → Stream A
flatten ((a , as) ∷ aass) = go a as (♭ aass) where
  go : {A : Set} → A → List A → Stream (A × List A) → Stream A
  go a []        aass = a ∷ ♯ flatten aass
  go a (b ∷ as)  aass = a ∷ ♯ go b as aass
names : Stream String
names = flatten $ zipWith cons letters $ "" ∷ ♯ Stream.map show (allNatsFrom 0)
  where
    cons : (Char × List Char) → String → (String × List String)
    cons (c , cs) suffix = appendSuffix c , map appendSuffix cs where
      appendSuffix : Char → String
      appendSuffix c  = fromList (c ∷ []) ++ suffix

    letters = Stream.repeat $ 'a' , toList "bcdefghijklmnopqrstuvwxyz"

    allNatsFrom : ℕ → Stream ℕ
    allNatsFrom k = k ∷ ♯ allNatsFrom (1 + k)
\end{code}
%<*name-context>
\begin{code}
nameContext : (Δ : Con) (Γ : Con) → State (Stream String) (Δ [ Name ] Γ)
\end{code}
%</name-context>
\begin{code}
nameContext Δ ε        =  return `ε
nameContext Δ (Γ ∙ σ)  =  nameContext Δ Γ >>= λ g →
                        get >>= λ names → put (tail names) >>
                        return (g `∙ mkName (head names))
\end{code}
%<*print>
\begin{code}
print : {Γ : Con} {σ : ty} (t : Γ ⊢ σ) → String
print {Γ} t = proj₁ $ (nameContext Γ Γ >>= runPrinter ∘ λ ρ → Printing ⊨⟦ t ⟧ ρ) names
\end{code}
%</print>
%<*pretty-test>
\begin{code}
pretty$ : {σ τ : ty} → print {Γ = ε ∙ σ `→ τ} (`λ $ `var (1+ zero) `$ `var zero) ≡ "λb. a (b)"
pretty$ = PEq.refl
\end{code}
%</pretty-test>
\begin{code}
infixl 10 _⟨_/var₀⟩

\end{code}
%<*eta>
\begin{code}
eta : {Γ : Con} {σ τ : ty} (t : Γ ⊢ σ `→ τ) → Γ ⊢ σ `→ τ
eta t = `λ $ wk^⊢ (step refl) t `$ `var zero
\end{code}
%</eta>
%<*beta-red>
\begin{code}
_⟨_/var₀⟩ : {Γ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
t ⟨ u /var₀⟩ = subst t $ pack `var `∙ u
\end{code}
%</beta-red>
\begin{code}

infix 5 _⊢[_]^ne_ _⊢[_]^nf_
mutual
\end{code}
%<*neutral>
\begin{code}
  data _⊢[_]^ne_ (Γ : Con) (R : ty → Set) (σ : ty) : Set where
    `var   : (v : σ ∈ Γ) → Γ ⊢[ R ]^ne σ
    _`$_   : {τ : ty} (t : Γ ⊢[ R ]^ne τ `→ σ) (u : Γ ⊢[ R ]^nf τ) → Γ ⊢[ R ]^ne σ
    `ifte  : (b : Γ ⊢[ R ]^ne `Bool) (l r : Γ ⊢[ R ]^nf σ) → Γ ⊢[ R ]^ne σ
\end{code}
%</neutral>
%<*normal>
\begin{code}
  data _⊢[_]^nf_ (Γ : Con) (R : ty → Set) : (σ : ty) → Set where
    `embed  : {σ : ty} (pr : R σ) (t : Γ ⊢[ R ]^ne σ) → Γ ⊢[ R ]^nf σ
    `⟨⟩     : Γ ⊢[ R ]^nf `Unit
    `tt     : Γ ⊢[ R ]^nf `Bool
    `ff     : Γ ⊢[ R ]^nf `Bool
    `λ      : {σ τ : ty} (b : Γ ∙ σ ⊢[ R ]^nf τ) → Γ ⊢[ R ]^nf (σ `→ τ)
\end{code}
%</normal>
\begin{code}

wk^ne : {Δ Γ : Con} (inc : Γ ⊆ Δ) {R : ty → Set} {σ : ty} (ne : Γ ⊢[ R ]^ne σ) → Δ ⊢[ R ]^ne σ
wk^nf : {Δ Γ : Con} (inc : Γ ⊆ Δ) {R : ty → Set} {σ : ty} (ne : Γ ⊢[ R ]^nf σ) → Δ ⊢[ R ]^nf σ
wk^ne inc (`var v)        = `var $′ wk^∈ inc v
wk^ne inc (ne `$ u)       = wk^ne inc ne `$ wk^nf inc u
wk^ne inc (`ifte ne l r)  = `ifte (wk^ne inc ne) (wk^nf inc l) (wk^nf inc r)

wk^nf inc (`embed pr t) = `embed pr $′ wk^ne inc t
wk^nf inc `⟨⟩           = `⟨⟩
wk^nf inc `tt           = `tt
wk^nf inc `ff           = `ff
wk^nf inc (`λ nf)       = `λ $′ wk^nf (pop! inc) nf

infix 5 [_,_]
[_,_] : {ℓ : Level} {Γ : Con} {τ : ty} {P : (σ : ty) (pr : σ ∈ Γ ∙ τ) → Set ℓ} →
        (p0 : P τ zero) →
        (pS : (σ : ty) (n : σ ∈ Γ) → P σ (1+ n)) →
        (σ : ty) (pr : σ ∈ Γ ∙ τ) → P σ pr
[ p0 , pS ] σ zero    = p0
[ p0 , pS ] σ (1+ n)  = pS σ n

mutual

  wk^nf-refl′ : {Γ : Con} {R : ty → Set} {σ : ty} {f : Γ ⊆ Γ} (prf : (σ : ty) (pr : σ ∈ Γ) → lookup f pr ≡ pr) →
                (t : Γ ⊢[ R ]^nf σ) → wk^nf f t ≡ t
  wk^nf-refl′ prf (`embed pr t)  = PEq.cong (`embed pr) $ wk^ne-refl′ prf t
  wk^nf-refl′ prf `⟨⟩            = PEq.refl
  wk^nf-refl′ prf `tt            = PEq.refl
  wk^nf-refl′ prf `ff            = PEq.refl
  wk^nf-refl′ prf (`λ t)         = PEq.cong `λ $ wk^nf-refl′ ([ PEq.refl , (λ σ → PEq.cong 1+_ ∘ prf σ) ]) t

  wk^ne-refl′ : {Γ : Con} {R : ty → Set} {σ : ty} {f : Γ ⊆ Γ} (prf : (σ : ty) (pr : σ ∈ Γ) → lookup f pr ≡ pr) →
                (t : Γ ⊢[ R ]^ne σ) → wk^ne f t ≡ t
  wk^ne-refl′ prf (`var v)       = PEq.cong `var $ prf _ v
  wk^ne-refl′ prf (t `$ u)       = PEq.cong₂ _`$_ (wk^ne-refl′ prf t) (wk^nf-refl′ prf u)
  wk^ne-refl′ prf (`ifte b l r)  = PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ (wk^ne-refl′ prf b) (wk^nf-refl′ prf l)) (wk^nf-refl′ prf r)

mutual

  wk^nf-trans′ : {Θ Δ Γ : Con} {R : ty → Set} {σ : ty} {inc₁ : Γ ⊆ Δ} {inc₂ : Δ ⊆ Θ}
                 {f : Γ ⊆ Θ} (prf : (σ : ty) (pr : σ ∈ Γ) → lookup (trans inc₁ inc₂) pr ≡ lookup f pr)
                 (t : Γ ⊢[ R ]^nf σ) →  wk^nf inc₂ (wk^nf inc₁ t) ≡ wk^nf f t
  wk^nf-trans′ prf (`embed pr t)  = PEq.cong (`embed pr) (wk^ne-trans′ prf t)
  wk^nf-trans′ prf `⟨⟩            = PEq.refl
  wk^nf-trans′ prf `tt            = PEq.refl
  wk^nf-trans′ prf `ff            = PEq.refl
  wk^nf-trans′ prf (`λ t)         = PEq.cong `λ $ wk^nf-trans′ ([ PEq.refl , (λ σ → PEq.cong 1+_ ∘ prf σ) ]) t

  wk^ne-trans′ : {Θ Δ Γ : Con} {R : ty → Set} {σ : ty} {inc₁ : Γ ⊆ Δ} {inc₂ : Δ ⊆ Θ}
                 {f : Γ ⊆ Θ} (prf : (σ : ty) (pr : σ ∈ Γ) → lookup (trans inc₁ inc₂) pr ≡ lookup f pr)
                 (t : Γ ⊢[ R ]^ne σ) →  wk^ne inc₂ (wk^ne inc₁ t) ≡ wk^ne f t
  wk^ne-trans′ prf (`var v)       = PEq.cong `var (prf _ v)
  wk^ne-trans′ prf (t `$ u)       = PEq.cong₂ _`$_ (wk^ne-trans′ prf t) (wk^nf-trans′ prf u)
  wk^ne-trans′ prf (`ifte b l r)  = PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ (wk^ne-trans′ prf b) (wk^nf-trans′ prf l)) (wk^nf-trans′ prf r)

wk^nf-refl : {Γ : Con} {R : ty → Set} {σ : ty} (t : Γ ⊢[ R ]^nf σ) → wk^nf refl t ≡ t
wk^nf-refl = wk^nf-refl′ (λ _ _ → PEq.refl)

wk^ne-refl : {Γ : Con} {R : ty → Set} {σ : ty} (t : Γ ⊢[ R ]^ne σ) → wk^ne refl t ≡ t
wk^ne-refl = wk^ne-refl′ (λ _ _ → PEq.refl)

wk^nf-trans : {Θ Δ Γ : Con} {R : ty → Set} {σ : ty} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ)
               (t : Γ ⊢[ R ]^nf σ) →  wk^nf inc₂ (wk^nf inc₁ t) ≡ wk^nf (trans inc₁ inc₂) t
wk^nf-trans inc₁ inc₂ = wk^nf-trans′ (λ _ _ → PEq.refl)

wk^ne-trans : {Θ Δ Γ : Con} {R : ty → Set} {σ : ty} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ)
               (t : Γ ⊢[ R ]^ne σ) →  wk^ne inc₂ (wk^ne inc₁ t) ≡ wk^ne (trans inc₁ inc₂) t
wk^ne-trans inc₁ inc₂ = wk^ne-trans′ (λ _ _ → PEq.refl)

\end{code}
%<*rel-betaiotaxieta>
\begin{code}
R^βιξη : ty → Set
R^βιξη `Bool  = ⊤
R^βιξη _      = ⊥
\end{code}
%</rel-betaiotaxieta>
\begin{code}

infix 5 _⊨^βιξη_

\end{code}
%<*sem-betaiotaxieta>
\begin{code}
_⊨^βιξη_ : (Γ : Con) (σ : ty) → Set
Γ ⊨^βιξη `Unit     = ⊤
Γ ⊨^βιξη `Bool     = Γ ⊢[ R^βιξη ]^nf `Bool
Γ ⊨^βιξη (σ `→ τ)  = {Δ : Con} → Γ ⊆ Δ → Δ ⊨^βιξη σ → Δ ⊨^βιξη τ
\end{code}
%</sem-betaiotaxieta>
%<*weak-betaiotaxieta>
\begin{code}
wk^βιξη : {Δ Γ : Con} (σ : ty) (inc : Γ ⊆ Δ) (T : Γ ⊨^βιξη σ) → Δ ⊨^βιξη σ
wk^βιξη `Unit     inc T = T
wk^βιξη `Bool     inc T = wk^nf inc T
wk^βιξη (σ `→ τ)  inc T = λ inc′ → T $′ trans inc inc′
\end{code}
%</weak-betaiotaxieta>
\begin{code}
infixr 5 _$^βιξη_

\end{code}
%<*apply-betaiotaxieta>
\begin{code}
_$^βιξη_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βιξη σ `→ τ) (u : Γ ⊨^βιξη σ) → Γ ⊨^βιξη τ
t $^βιξη u = t refl u
\end{code}
%</apply-betaiotaxieta>
\begin{code}
mutual

\end{code}
%<*var0-betaiotaxieta>
\begin{code}
  var‿0^βιξη : {Γ : Con} {σ : ty} → Γ ∙ σ ⊨^βιξη σ
  var‿0^βιξη = reflect^βιξη _ $′ `var zero
\end{code}
%</var0-betaiotaxieta>
%<*reflect-betaiotaxieta>
\begin{code}
  reflect^βιξη : {Γ : Con} (σ : ty) (t : Γ ⊢[ R^βιξη ]^ne σ) → Γ ⊨^βιξη σ
  reflect^βιξη `Unit     t = ⟨⟩
  reflect^βιξη `Bool     t = `embed _ t
  reflect^βιξη (σ `→ τ)  t = λ inc u → reflect^βιξη τ $′ wk^ne inc t `$ reify^βιξη σ u
\end{code}
%</reflect-betaiotaxieta>
%<*reify-betaiotaxieta>
\begin{code}
  reify^βιξη : {Γ : Con} (σ : ty) (T : Γ ⊨^βιξη σ) → Γ ⊢[ R^βιξη ]^nf σ
  reify^βιξη `Unit     T = `⟨⟩
  reify^βιξη `Bool     T = T
  reify^βιξη (σ `→ τ)  T = `λ $′ reify^βιξη τ $′ T (step refl) var‿0^βιξη
\end{code}
%</reify-betaiotaxieta>
%<*ifte-betaiotaxieta>
\begin{code}
ifte^βιξη : {Γ : Con} {σ : ty} (b : Γ ⊨^βιξη `Bool) (l r : Γ ⊨^βιξη σ) → Γ ⊨^βιξη σ
ifte^βιξη `tt           l r = l
ifte^βιξη `ff           l r = r
ifte^βιξη (`embed _ T)  l r = reflect^βιξη _ $′ `ifte T (reify^βιξη _ l) (reify^βιξη _ r)
\end{code}
%</ifte-betaiotaxieta>
%<*normalise-betaiotaxieta>
\begin{code}
Normalise^βιξη : Semantics _⊨^βιξη_ _⊨^βιξη_
Normalise^βιξη = record
  { embed = reflect^βιξη _ ∘ `var; wk = wk^βιξη _; ⟦var⟧ = id
  ; _⟦$⟧_ = _$^βιξη_; ⟦λ⟧ = id
  ; ⟦⟨⟩⟧ = ⟨⟩; ⟦tt⟧ = `tt; ⟦ff⟧ = `ff; ⟦ifte⟧  = ifte^βιξη }
\end{code}
%</normalise-betaiotaxieta>
%<*norm-betaiotaxieta>
\begin{code}
norm^βιξη : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢[ R^βιξη ]^nf σ
norm^βιξη σ t = reify^βιξη σ $′ Normalise^βιξη ⊨eval t
\end{code}
%</norm-betaiotaxieta>
\begin{code}
R^βιξ : ty → Set
R^βιξ _ = ⊤

infix 5 _⊨^βιξ_ _⊨^βιξ⋆_
mutual

\end{code}
%<*rel-betaiotaxi>
\begin{code}
  _⊨^βιξ_   : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βιξ σ  = Γ ⊢[ R^βιξ ]^ne σ ⊎ Γ ⊨^βιξ⋆ σ

  _⊨^βιξ⋆_  : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βιξ⋆ `Unit     = ⊤
  Γ ⊨^βιξ⋆ `Bool     = Bool
  Γ ⊨^βιξ⋆ (σ `→ τ)  = {Δ : Con} → Γ ⊆ Δ → Δ ⊨^βιξ σ → Δ ⊨^βιξ τ
\end{code}
%</rel-betaiotaxi>
%<*reify-betaiotaxieta>
\begin{code}
wk^βιξ⋆ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^βιξ⋆ σ) → Δ ⊨^βιξ⋆ σ
wk^βιξ⋆ inc {`Unit   } T = T
wk^βιξ⋆ inc {`Bool   } T = T
wk^βιξ⋆ inc {σ `→ τ  } T = λ inc′ → T $′ trans inc inc′

wk^βιξ : {Δ Γ : Con} {σ : ty} (inc : Γ ⊆ Δ) (T : Γ ⊨^βιξ σ) → Δ ⊨^βιξ σ
wk^βιξ inc (inj₁ ne)  = inj₁ $ wk^ne inc ne
wk^βιξ inc (inj₂ T)   = inj₂ $ wk^βιξ⋆ inc T

\end{code}
%<*reflect-betaiotaxi>
\begin{code}
reflect^βιξ : {Γ : Con} (σ : ty) (t : Γ ⊢[ R^βιξ ]^ne σ) → Γ ⊨^βιξ σ
reflect^βιξ σ = inj₁
\end{code}
%</reflect-betaiotaxi>
\begin{code}
mutual

\end{code}
%<*reify-betaiotaxi>
\begin{code}
  reify^βιξ⋆ : {Γ : Con} (σ : ty) (T : Γ ⊨^βιξ⋆ σ) → Γ ⊢[ R^βιξ ]^nf σ
  reify^βιξ⋆ `Unit     T = `⟨⟩
  reify^βιξ⋆ `Bool     T = if T then `tt else `ff
  reify^βιξ⋆ (σ `→ τ)  T = `λ $′ reify^βιξ τ $′ T (step refl) var‿0^βιξ
    where var‿0^βιξ = inj₁ $ `var zero

  reify^βιξ : {Γ : Con} (σ : ty) (T : Γ ⊨^βιξ σ) → Γ ⊢[ R^βιξ ]^nf σ
  reify^βιξ σ (inj₁ ne)  = `embed _ ne
  reify^βιξ σ (inj₂ T)   = reify^βιξ⋆ σ T
\end{code}
%</reify-betaiotaxi>
\begin{code}
infixr 5 _$^βιξ_

\end{code}
%<*apply-betaiotaxi>
\begin{code}
_$^βιξ_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βιξ (σ `→ τ)) (u : Γ ⊨^βιξ σ) → Γ ⊨^βιξ τ
(inj₁ ne)  $^βιξ u = inj₁ $ ne `$ reify^βιξ _ u
(inj₂ F)   $^βιξ u = F refl u
\end{code}
%</apply-betaiotaxi>
%<*ifte-betaiotaxi>
\begin{code}
ifte^βιξ : {Γ : Con} {σ : ty} (b : Γ ⊨^βιξ `Bool) (l r : Γ ⊨^βιξ σ) → Γ ⊨^βιξ σ
ifte^βιξ (inj₁ ne) l r = inj₁ $ `ifte ne (reify^βιξ _ l) (reify^βιξ _ r)
ifte^βιξ (inj₂ T)  l r = if T then l else r
\end{code}
%</ifte-betaiotaxi>
%<*normalise-betaiotaxi>
\begin{code}
Normalise^βιξ : Semantics _⊨^βιξ_ _⊨^βιξ_
Normalise^βιξ = record
  { embed = reflect^βιξ _ ∘ `var; wk = wk^βιξ; ⟦var⟧   = id
  ; _⟦$⟧_ = _$^βιξ_; ⟦λ⟧ = inj₂
  ; ⟦⟨⟩⟧ = inj₂ ⟨⟩; ⟦tt⟧ = inj₂ true; ⟦ff⟧ = inj₂ false; ⟦ifte⟧  = ifte^βιξ }
\end{code}
%</normalise-betaiotaxi>
%<*norm-betaiotaxi>
\begin{code}
norm^βιξ : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢[ R^βιξ ]^nf σ
norm^βιξ σ t = reify^βιξ σ $′ Normalise^βιξ ⊨eval t
\end{code}
%</norm-betaiotaxi>
\begin{code}
infix 5 _⊢^whne_ _⊢^whnf_

\end{code}
%</norm-betaiotaxi>
%<*whneutral>
\begin{code}
data _⊢^whne_ (Γ : Con) (σ : ty) : Set where
  `var   : (v : σ ∈ Γ) → Γ ⊢^whne σ
  _`$_   : {τ : ty} (t : Γ ⊢^whne (τ `→ σ)) (u : Γ ⊢ τ) → Γ ⊢^whne σ
  `ifte  : (b : Γ ⊢^whne `Bool) (l r : Γ ⊢ σ) → Γ ⊢^whne σ
\end{code}
%</whneutral>
%<*whnormal>
\begin{code}
data _⊢^whnf_ (Γ : Con) : (σ : ty) → Set where
  `embed   : {σ : ty} (t : Γ ⊢^whne σ) → Γ ⊢^whnf σ
  `⟨⟩      : Γ ⊢^whnf `Unit
  `tt `ff  : Γ ⊢^whnf `Bool
  `λ       : {σ τ : ty} (b : Γ ∙ σ ⊢ τ) → Γ ⊢^whnf (σ `→ τ)
\end{code}
%</whnormal>
\begin{code}

wk^whne : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^whne σ) → Δ ⊢^whne σ
wk^whnf : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (ne : Γ ⊢^whnf σ) → Δ ⊢^whnf σ
wk^whne inc (`var v)        = `var $′ wk^∈ inc v
wk^whne inc (ne `$ u)       = wk^whne inc ne `$ wk^⊢ inc u
wk^whne inc (`ifte ne l r)  = `ifte (wk^whne inc ne) (wk^⊢ inc l) (wk^⊢ inc r)

wk^whnf inc (`embed t)  = `embed $′ wk^whne inc t
wk^whnf inc `⟨⟩         = `⟨⟩
wk^whnf inc `tt         = `tt
wk^whnf inc `ff         = `ff
wk^whnf inc (`λ b)      = `λ $′ wk^⊢ (pop! inc) b

erase^whne : {Γ : Con} {σ : ty} (t : Γ ⊢^whne σ) → Γ ⊢ σ
erase^whne (`var v)       = `var v
erase^whne (t `$ u)       = erase^whne t `$ u
erase^whne (`ifte t l r)  = `ifte (erase^whne t) l r

infix 5 _⊨^βι_ _⊨^βι⋆_

mutual
\end{code}
%<*sem-betaiota>
\begin{code}
  _⊨^βι_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βι σ  = Γ ⊢ σ  × (Γ ⊢^whne σ ⊎ Γ ⊨^βι⋆ σ)

  _⊨^βι⋆_ : (Γ : Con) (σ : ty) → Set
  Γ ⊨^βι⋆ `Unit     = ⊤
  Γ ⊨^βι⋆ `Bool     = Bool
  Γ ⊨^βι⋆ (σ `→ τ)  = {Δ : Con} → Γ ⊆ Δ → Δ ⊨^βι σ → Δ ⊨^βι τ
\end{code}
%</sem-betaiota>
\begin{code}

wk^βι⋆ : {Δ Γ : Con} (inc : Γ ⊆ Δ) {σ : ty} (T : Γ ⊨^βι⋆ σ) → Δ ⊨^βι⋆ σ
wk^βι⋆ inc {`Unit   } T = T
wk^βι⋆ inc {`Bool   } T = T
wk^βι⋆ inc {σ `→ τ  } T = λ inc′ → T $′ trans inc inc′

wk^βι : {Δ Γ : Con}{σ : ty} (inc : Γ ⊆ Δ) (T : Γ ⊨^βι σ) → Δ ⊨^βι σ
wk^βι inc (t , inj₁ ne)  = wk^⊢ inc t , inj₁ (wk^whne inc ne)
wk^βι inc (t , inj₂ T)   = wk^⊢ inc t , inj₂ (wk^βι⋆ inc T)

reflect^βι : {Γ : Con} (σ : ty) (t : Γ ⊢^whne σ) → Γ ⊨^βι σ
reflect^βι σ t = erase^whne t , inj₁ t

mutual

  reify^βι⋆ : {Γ : Con} (σ : ty) (T : Γ ⊨^βι⋆ σ) → Γ ⊢^whnf σ
  reify^βι⋆ `Unit     T = `⟨⟩
  reify^βι⋆ `Bool     T = if T then `tt else `ff
  reify^βι⋆ (σ `→ τ)  T = `λ $ proj₁ $ T (step refl) var‿0^βι
    where var‿0^βι = reflect^βι _ $ `var zero

  reify^βι : {Γ : Con} (σ : ty) (T : Γ ⊨^βι σ) → Γ ⊢^whnf σ
  reify^βι σ (t , inj₁ ne) = `embed ne
  reify^βι σ (t , inj₂ T)  = reify^βι⋆ σ T

infixr 5 _$^βι_

_$^βι_ : {Γ : Con} {σ τ : ty} (t : Γ ⊨^βι σ `→ τ) (u : Γ ⊨^βι σ) → Γ ⊨^βι τ
(t , inj₁ ne)  $^βι (u , U) = t `$ u , inj₁ (ne `$ u)
(t , inj₂ T)   $^βι (u , U) = t `$ u , proj₂ (T refl (u , U))

ifte^βι : {Γ : Con} {σ : ty} (b : Γ ⊨^βι `Bool) (l r : Γ ⊨^βι σ) → Γ ⊨^βι σ
ifte^βι (b , inj₁ ne)  (l , L) (r , R) = `ifte b l r , inj₁ (`ifte ne l r)
ifte^βι (b , inj₂ B)   (l , L) (r , R) = `ifte b l r , (if B then L else R)

\end{code}
%<*normalise-betaiota>
\begin{code}
Normalise^βι : Semantics _⊨^βι_ _⊨^βι_
Normalise^βι = record
  { embed = reflect^βι _ ∘ `var; wk = wk^βι; ⟦var⟧ = id
  ; _⟦$⟧_ = _$^βι_; ⟦λ⟧ = λ t → `λ (proj₁ $ t (step refl) (reflect^βι _ $ `var zero)) , inj₂ t
  ; ⟦⟨⟩⟧ = `⟨⟩ , inj₂ ⟨⟩; ⟦tt⟧ = `tt  , inj₂ true; ⟦ff⟧ = `ff  , inj₂ false; ⟦ifte⟧  = ifte^βι }
\end{code}
%</normalise-betaiota>
\begin{code}

norm^βι : {Γ : Con} (σ : ty) (t : Γ ⊢ σ) → Γ ⊢^whnf σ
norm^βι σ t = reify^βι σ $′ Normalise^βι ⊨eval t

record `∀[_] {ℓ^A ℓ^B ℓ^R : Level} {𝓔^A : Con → ty → Set ℓ^A} {𝓔^B : Con → ty → Set ℓ^B}
             (𝓔^R : {Γ : Con} {σ : ty} (u^A : 𝓔^A Γ σ) (u^B : 𝓔^B Γ σ) → Set ℓ^R)
             {Γ Δ : Con} (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Δ [ 𝓔^B ] Γ) : Set ℓ^R where
  constructor pack^R
  field lookup^R : {σ : ty} (v : σ ∈ Γ) → 𝓔^R (lookup ρ^A v) (lookup ρ^B v)
open `∀[_]

\end{code}
%<*sync-record>
\begin{code}
record Synchronisable {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^RE ℓ^RM : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} (𝓢^A : Semantics 𝓔^A 𝓜^A) (𝓢^B : Semantics 𝓔^B 𝓜^B)
  (𝓔^R  : {Γ : Con} {σ : ty} → 𝓔^A Γ σ → 𝓔^B Γ σ → Set ℓ^RE)
  (𝓜^R  : {Γ Δ : Con} {σ : ty} → Γ ⊢ σ → Δ [ 𝓔^A ] Γ → Δ [ 𝓔^B ] Γ → 𝓜^A Δ σ → 𝓜^B Δ σ → Set ℓ^RM)
  : Set (ℓ^RE ⊔ ℓ^RM ⊔ ℓ^EA ⊔ ℓ^EB ⊔ ℓ^MA ⊔ ℓ^MB) where
\end{code}
%</sync-record>
\begin{code}
  module 𝓢^A = Semantics 𝓢^A
  module 𝓢^B = Semantics 𝓢^B

\end{code}
%<*sync-sync>
\begin{code}
  Sync : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Δ [ 𝓔^B ] Γ) → Set ℓ^RM
  Sync t ρ^A ρ^B = 𝓜^R t ρ^A ρ^B (𝓢^A ⊨⟦ t ⟧ ρ^A) (𝓢^B ⊨⟦ t ⟧ ρ^B)
\end{code}
%</sync-sync>
%<*sync-kripke>
\begin{code}
  Kripke^R : (Γ Δ : Con) (σ τ : ty) (t : (Γ ∙ σ) ⊢ τ) (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Δ [ 𝓔^B ] Γ) → Set (ℓ^RM ⊔ (ℓ^RE ⊔ (ℓ^EB ⊔ ℓ^EA)))
  Kripke^R Γ Δ σ τ t ρ^A ρ^B = {Θ : Con} (inc : Δ ⊆ Θ) {u^A : 𝓔^A Θ σ} {u^B : 𝓔^B Θ σ} (u^R : 𝓔^R u^A u^B) → Sync t (wk[ 𝓢^A.wk ] inc ρ^A `∙ u^A) (wk[ 𝓢^B.wk ] inc ρ^B `∙ u^B)
\end{code}
%</sync-kripke>
\begin{code}
  field

\end{code}
%<*sync-env>
\begin{code}
    𝓔^R‿wk  :  {Γ Δ Θ : Con} (inc : Δ ⊆ Θ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} (ρ^R : `∀[ 𝓔^R ] ρ^A ρ^B) →
               `∀[ 𝓔^R ] (wk[ 𝓢^A.wk ] inc ρ^A) (wk[ 𝓢^B.wk ] inc ρ^B)
\end{code}
%</sync-env>
%<*sync-var>
\begin{code}
    R⟦var⟧    :  {Γ Δ : Con} {σ : ty} (v : σ ∈ Γ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} (ρ^R : `∀[ 𝓔^R ] ρ^A ρ^B) → Sync (`var v) ρ^A ρ^B
\end{code}
%</sync-var>
%<*sync-lam>
\begin{code}
    R⟦λ⟧      :  {Γ Δ : Con} {σ τ : ty} {b : (Γ ∙ σ) ⊢ τ} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} → Kripke^R Γ Δ σ τ b ρ^A ρ^B → `∀[ 𝓔^R ] ρ^A ρ^B → Sync (`λ b) ρ^A ρ^B
\end{code}
%</sync-lam>
%<*sync-app>
\begin{code}
    R⟦$⟧      :  {Γ Δ : Con} {σ τ : ty} {t : Γ ⊢ (σ `→ τ)} {u : Γ ⊢ σ} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} → Sync t ρ^A ρ^B → Sync u ρ^A ρ^B → `∀[ 𝓔^R ] ρ^A ρ^B → Sync (t `$ u) ρ^A ρ^B
\end{code}
%</sync-app>
\begin{code}

    R⟦⟨⟩⟧     :  {Γ Δ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} → `∀[ 𝓔^R ] ρ^A ρ^B → Sync `⟨⟩ ρ^A ρ^B
    R⟦tt⟧     :  {Γ Δ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} → `∀[ 𝓔^R ] ρ^A ρ^B → Sync `tt ρ^A ρ^B
    R⟦ff⟧     :  {Γ Δ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} → `∀[ 𝓔^R ] ρ^A ρ^B → Sync `ff ρ^A ρ^B
    R⟦ifte⟧   :  {Γ Δ : Con} {σ : ty} {b : Γ ⊢ `Bool} {l r : Γ ⊢ σ} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} → Sync b ρ^A ρ^B → Sync l ρ^A ρ^B → Sync r ρ^A ρ^B →
                 `∀[ 𝓔^R ] ρ^A ρ^B → Sync (`ifte b l r) ρ^A ρ^B
infixl 10 _∙^R_
\end{code}
%<*sync-cons>
\begin{code}
_∙^R_ :  {ℓ^EA ℓ^EB ℓ^ER : Level} {𝓔^A : Con → ty → Set ℓ^EA} {𝓔^B : Con → ty → Set ℓ^EB} {𝓔^R : {Γ : Con} {σ : ty} → 𝓔^A Γ σ → 𝓔^B Γ σ → Set ℓ^ER} {Δ Γ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} {σ : ty} {u^A : 𝓔^A Δ σ} {u^B : 𝓔^B Δ σ} → `∀[ 𝓔^R ] ρ^A ρ^B → 𝓔^R u^A u^B → `∀[ 𝓔^R ] (ρ^A `∙ u^A) (ρ^B `∙ u^B)
lookup^R (ρ^R ∙^R u^R) zero    = u^R
lookup^R (ρ^R ∙^R u^R) (1+ v)  = lookup^R ρ^R v
\end{code}
%</sync-cons>
%<*synced-record>
\begin{code}
module Synchronised {ℓ^EA ℓ^MA ℓ^EB ℓ^MB : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓢^A : Semantics 𝓔^A 𝓜^A} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} {𝓢^B : Semantics 𝓔^B 𝓜^B} {ℓ^RE ℓ^RM : Level} {𝓔^R : {Γ : Con} {σ : ty} (u^A : 𝓔^A Γ σ) (u^B : 𝓔^B Γ σ) → Set ℓ^RE} {𝓜^R : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Δ [ 𝓔^B ] Γ) (mA : 𝓜^A Δ σ) (mB : 𝓜^B Δ σ) → Set ℓ^RM} (𝓡 : Synchronisable 𝓢^A 𝓢^B 𝓔^R 𝓜^R) where
\end{code}
%</synced-record>
\begin{code}
  open Synchronisable 𝓡
\end{code}
%<*sync-lemma>
\begin{code}
  lemma :  {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Δ [ 𝓔^B ] Γ} (ρ^R : `∀[ 𝓔^R ] ρ^A ρ^B) → Sync t ρ^A ρ^B
  lemma (`var v)       ρ^R = R⟦var⟧ v ρ^R
  lemma (f `$ t)       ρ^R = R⟦$⟧ (lemma f ρ^R) (lemma t ρ^R) ρ^R
  lemma (`λ t)         ρ^R = R⟦λ⟧ (λ inc u^R → lemma t $ 𝓔^R‿wk inc ρ^R ∙^R u^R) ρ^R
  lemma `⟨⟩            ρ^R = R⟦⟨⟩⟧ ρ^R
  lemma `tt            ρ^R = R⟦tt⟧ ρ^R
  lemma `ff            ρ^R = R⟦ff⟧ ρ^R
  lemma (`ifte b l r)  ρ^R = R⟦ifte⟧ (lemma b ρ^R) (lemma l ρ^R) (lemma r ρ^R) ρ^R
\end{code}
%</sync-lemma>
%<*sync-rensub>
\begin{code}
SynchronisableRenamingSubstitution :  Synchronisable Renaming Substitution
                                      (λ v t → `var v ≡ t) (λ _ _ _ → _≡_)
\end{code}
%</sync-rensub>
\begin{code}
SynchronisableRenamingSubstitution =
  record
    { 𝓔^R‿wk  = λ inc ρ^R → pack^R $ PEq.cong (wk^⊢ inc) ∘ lookup^R ρ^R
    ; R⟦var⟧    = λ v ρ^R → lookup^R ρ^R v
    ; R⟦$⟧      = λ eqf eqt _ → PEq.cong₂ _`$_ eqf eqt
    ; R⟦λ⟧      = λ r _ → PEq.cong `λ (r (step refl) PEq.refl)
    ; R⟦⟨⟩⟧     = const PEq.refl
    ; R⟦tt⟧     = const PEq.refl
    ; R⟦ff⟧     = const PEq.refl
    ; R⟦ifte⟧   = λ eqb eql eqr _ → PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ eqb eql) eqr
    }
\end{code}
%<*sync-renissub>
\begin{code}
RenamingIsASubstitution : {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) (ρ : Γ ⊆ Δ) →
  Renaming ⊨⟦ t ⟧ ρ ≡ Substitution ⊨⟦ t ⟧ trans ρ (pack `var)
RenamingIsASubstitution t ρ = lemma t (pack^R $ λ _ → PEq.refl)
  where open Synchronised SynchronisableRenamingSubstitution
\end{code}
%</sync-renissub>
%<*eqrel>
\begin{code}
EQREL : (Γ : Con) (σ : ty) (T U : Γ ⊨^βιξη σ) → Set
EQREL Γ `Unit     T U = ⊤
EQREL Γ `Bool     T U = T ≡ U
EQREL Γ (σ `→ τ)  T U =  {Δ : Con} (inc : Γ ⊆ Δ) {V W : Δ ⊨^βιξη σ} (eqVW : EQREL Δ σ V W) →
                         EQREL Δ τ (T inc V) (U inc W)
\end{code}
%</eqrel>
%<*eqrel-sym>
\begin{code}
symEQREL : {Γ : Con} (σ : ty) {S T : Γ ⊨^βιξη σ} → EQREL Γ σ S T → EQREL Γ σ T S
\end{code}
%</eqrel-sym>
\begin{code}
symEQREL `Unit     eq = ⟨⟩
symEQREL `Bool     eq = PEq.sym eq
symEQREL (σ `→ τ)  eq = λ inc eqVW → symEQREL τ (eq inc (symEQREL σ eqVW))
\end{code}
%<*eqrel-trans>
\begin{code}
transEQREL : {Γ : Con} (σ : ty) {S T U : Γ ⊨^βιξη σ} → EQREL Γ σ S T → EQREL Γ σ T U → EQREL Γ σ S U
\end{code}
%</eqrel-trans>
\begin{code}
  -- We are in PER so reflEQREL is not provable
  -- but as soon as EQREL σ V W then EQREL σ V V
reflEQREL : {Γ : Con} (σ : ty) {S T : Γ ⊨^βιξη σ} → EQREL Γ σ S T → EQREL Γ σ S S

transEQREL `Unit     eq₁ eq₂ = ⟨⟩
transEQREL `Bool     eq₁ eq₂ = PEq.trans eq₁ eq₂
transEQREL (σ `→ τ)  eq₁ eq₂ =
  λ inc eqVW → transEQREL τ (eq₁ inc (reflEQREL σ eqVW)) (eq₂ inc eqVW)

reflEQREL σ eq = transEQREL σ eq (symEQREL σ eq)
\end{code}
%<*eqrel-weak>
\begin{code}
wk^EQREL :  {Δ Γ : Con} (σ : ty) (inc : Γ ⊆ Δ) {T U : Γ ⊨^βιξη σ} → EQREL Γ σ T U → EQREL Δ σ (wk^βιξη σ inc T) (wk^βιξη σ inc U)
\end{code}
%</eqrel-weak>
\begin{code}
wk^EQREL `Unit     inc eq = ⟨⟩
wk^EQREL `Bool     inc eq = PEq.cong (wk^nf inc) eq
wk^EQREL (σ `→ τ)  inc eq = λ inc′ eqVW → eq (trans inc inc′) eqVW
\end{code}
%<*eqrel-reify-reflect>
\begin{code}
reify^EQREL    :  {Γ : Con} (σ : ty) {T U : Γ ⊨^βιξη σ} → EQREL Γ σ T U → reify^βιξη σ T ≡ reify^βιξη σ U
reflect^EQREL  :  {Γ : Con} (σ : ty) {t u : Γ ⊢[ R^βιξη ]^ne σ} → t ≡ u → EQREL Γ σ (reflect^βιξη σ t) (reflect^βιξη σ u)
\end{code}
%</eqrel-reify-reflect>
\begin{code}
reify^EQREL `Unit     EQTU = PEq.refl
reify^EQREL `Bool     EQTU = EQTU
reify^EQREL (σ `→ τ)  EQTU = PEq.cong `λ $ reify^EQREL τ $ EQTU (step refl) $ reflect^EQREL σ PEq.refl

reflect^EQREL `Unit     eq = ⟨⟩
reflect^EQREL `Bool     eq = PEq.cong (`embed _) eq
reflect^EQREL (σ `→ τ)  eq = λ inc rel → reflect^EQREL τ $ PEq.cong₂ _`$_ (PEq.cong (wk^ne inc) eq) (reify^EQREL σ rel)

ifteRelNorm :
      let open Semantics Normalise^βιξη in
      {Γ : Con} {σ : ty} {b^A b^B : Γ ⊨^βιξη `Bool} {l^A l^B r^A r^B : Γ ⊨^βιξη σ} →
      EQREL Γ `Bool b^A b^B → EQREL Γ σ l^A l^B → EQREL Γ σ r^A r^B →
      EQREL Γ σ (⟦ifte⟧ b^A l^A r^A) (⟦ifte⟧ b^B l^B r^B)
ifteRelNorm {b^A = `tt}         PEq.refl l^R r^R = l^R
ifteRelNorm {b^A = `ff}         PEq.refl l^R r^R = r^R
ifteRelNorm {b^A = `embed _ ne} PEq.refl l^R r^R =
  reflect^EQREL _ (PEq.cong₂ (`ifte ne) (reify^EQREL _ l^R) (reify^EQREL _ r^R))
\end{code}
%<*sync-normalise>
\begin{code}
SynchronisableNormalise :  Synchronisable Normalise^βιξη Normalise^βιξη
                           (EQREL _ _) (λ _ _ _ → EQREL _ _)
\end{code}
%</sync-normalise>
\begin{code}
SynchronisableNormalise =
  record  { 𝓔^R‿wk  = λ inc ρ^R → pack^R $ wk^EQREL _ inc ∘ lookup^R ρ^R
          ; R⟦var⟧   = λ v ρ^R → lookup^R ρ^R v
          ; R⟦$⟧     = λ f t _ → f refl t
          ; R⟦λ⟧     = const
          ; R⟦⟨⟩⟧    = const ⟨⟩
          ; R⟦tt⟧    = const PEq.refl
          ; R⟦ff⟧    = const PEq.refl
          ; R⟦ifte⟧  = λ b l r _ → ifteRelNorm b l r
          }
\end{code}
%</refl-normalise>
\begin{code}
refl^βιξη :  {Γ Δ : Con} {σ : ty} (t : Γ ⊢ σ) {ρ^A ρ^B : Δ [ _⊨^βιξη_ ] Γ} (ρ^R : `∀[ EQREL _ _ ] ρ^A ρ^B) →
             EQREL Δ σ (Normalise^βιξη ⊨⟦ t ⟧ ρ^A) (Normalise^βιξη ⊨⟦ t ⟧ ρ^B)
refl^βιξη t ρ^R = lemma t ρ^R where open Synchronised SynchronisableNormalise
\end{code}
%</refl-normalise>
\begin{code}
\end{code}
%<*fusable-record>
\begin{code}
record Fusable
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REBC ℓ^RM : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} {𝓜^C : (Γ : Con) (σ : ty) → Set ℓ^MC} (𝓢^A : Semantics 𝓔^A 𝓜^A) (𝓢^B : Semantics 𝓔^B 𝓜^B) (𝓢^C : Semantics 𝓔^C 𝓜^C)
  (𝓔^R‿BC : {Γ : Con} {σ : ty} (e^B : 𝓔^B Γ σ) (e^C : 𝓔^C Γ σ) → Set ℓ^REBC)
  (𝓔^R :  {Θ Δ Γ : Con} (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Θ [ 𝓔^B ] Δ) (ρ^C : Θ [ 𝓔^C ] Γ) → Set ℓ^RE)
  (𝓜^R : {Γ : Con} {σ : ty} (m^B : 𝓜^B Γ σ) (m^C : 𝓜^C Γ σ) → Set ℓ^RM)
  : Set (ℓ^RM ⊔ ℓ^RE ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA ⊔ ℓ^MA ⊔ ℓ^REBC) where
\end{code}
%</fusable-record>
\begin{code}

  module 𝓢^A = Semantics 𝓢^A
  module 𝓢^B = Semantics 𝓢^B
  module 𝓢^C = Semantics 𝓢^C
  field
\end{code}
%<*fusable-reify>
\begin{code}
    reify^A    : {Γ : Con} {σ : ty} (m : 𝓜^A Γ σ) → Γ ⊢ σ
\end{code}
%</fusable-reify>
%</fusable-cons>
\begin{code}
    𝓔^R‿∙   :  {Γ Δ Θ : Con} {σ : ty} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} {u^B : 𝓔^B Θ σ} {u^C : 𝓔^C Θ σ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) (u^R : 𝓔^R‿BC u^B u^C) →
               𝓔^R  (wk[ 𝓢^A.wk ] (step refl) ρ^A `∙ 𝓢^A.embed zero)
                    (ρ^B `∙ u^B) (ρ^C `∙ u^C)
\end{code}
%</fusable-cons>
%<*fusable-weak>
\begin{code}
    𝓔^R‿wk  :  {Γ Δ Θ E : Con} (inc : Θ ⊆ E) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
               𝓔^R ρ^A (wk[ 𝓢^B.wk ] inc ρ^B) (wk[ 𝓢^C.wk ] inc ρ^C)
\end{code}
%</fusable-weak>
%<*fusable-var>
\begin{code}
    R⟦var⟧  :  {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
               𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A.⟦var⟧ (lookup ρ^A v)) ⟧ ρ^B) (𝓢^C.⟦var⟧ (lookup ρ^C v))
\end{code}
%</fusable-var>
%<*fusable-lam>
\begin{code}
    R⟦λ⟧    :
      {Γ Δ Θ : Con} {σ τ : ty} (t : Γ ∙ σ ⊢ τ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
      (r :  {E : Con} (inc : Θ ⊆ E) {u^B : 𝓔^B E σ} {u^C : 𝓔^C E σ} (u^R : 𝓔^R‿BC u^B u^C) →
            let  ρ^A′ =  wk[ 𝓢^A.wk ] (step refl) ρ^A `∙ 𝓢^A.embed zero
                 ρ^B′ =  wk[ 𝓢^B.wk ] inc ρ^B `∙ u^B
                 ρ^C′ =  wk[ 𝓢^C.wk ] inc ρ^C `∙ u^C
            in 𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ t ⟧ ρ^A′) ⟧ ρ^B′) (𝓢^C ⊨⟦ t ⟧ ρ^C′)) →
      𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ `λ t ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ `λ t ⟧ ρ^C)
\end{code}
%</fusable-lam>
\begin{code}
    R⟦$⟧    : {Γ Δ Θ : Con} {σ τ : ty} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ)
            {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} →
             (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ f ⟧ ρ^A) ⟧ ρ^B)
                   (𝓢^C ⊨⟦ f ⟧ ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ t ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ t ⟧ ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ f `$ t ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ f `$ t ⟧ ρ^C)

    R⟦⟨⟩⟧   : {Γ Δ Θ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} →
             (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ `⟨⟩ ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ `⟨⟩ ⟧ ρ^C)
    R⟦tt⟧   : {Γ Δ Θ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} →
             (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ `tt ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ `tt ⟧ ρ^C)
    R⟦ff⟧   : {Γ Δ Θ : Con} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} →
             (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ `ff ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ `ff ⟧ ρ^C)
    R⟦ifte⟧ : {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
            {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} →
             (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ b ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ b ⟧ ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ l ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ l ⟧ ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ r ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ r ⟧ ρ^C) →
            𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ `ifte b l r ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ `ifte b l r ⟧ ρ^C)
\end{code}
%<*fusion-module>
\begin{code}
module Fusion {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REB ℓ^RM : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} {𝓜^A : (Γ : Con) (σ : ty) → Set ℓ^MA} {𝓜^B : (Γ : Con) (σ : ty) → Set ℓ^MB} {𝓜^C : (Γ : Con) (σ : ty) → Set ℓ^MC} {𝓢^A : Semantics 𝓔^A 𝓜^A} {𝓢^B : Semantics 𝓔^B 𝓜^B} {𝓢^C : Semantics 𝓔^C 𝓜^C} {𝓔^R‿BC : {Γ : Con} {σ : ty} (e^B : 𝓔^B Γ σ) (e^C : 𝓔^C Γ σ) → Set ℓ^REB} {𝓔^R : {Θ Δ Γ : Con} (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Θ [ 𝓔^B ] Δ) (ρ^C : Θ [ 𝓔^C ] Γ) → Set ℓ^RE} {𝓜^R : {Γ : Con} {σ : ty} (mB : 𝓜^B Γ σ) (mC : 𝓜^C Γ σ) → Set ℓ^RM} (fusable : Fusable 𝓢^A 𝓢^B 𝓢^C 𝓔^R‿BC 𝓔^R 𝓜^R) where
  open Fusable fusable
\end{code}
%</fusion-module>
%<*fusion-lemma>
\begin{code}
  lemma :  {Γ Δ Θ : Con} {σ : ty} (t : Γ ⊢ σ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
           𝓜^R (𝓢^B ⊨⟦ reify^A (𝓢^A ⊨⟦ t ⟧ ρ^A) ⟧ ρ^B) (𝓢^C ⊨⟦ t ⟧ ρ^C)
\end{code}
%</fusion-lemma>
\begin{code}
  lemma (`var v)       ρ^R = R⟦var⟧ v ρ^R
  lemma (f `$ t)       ρ^R = R⟦$⟧ f t ρ^R (lemma f ρ^R) (lemma t ρ^R)
  lemma (`λ t)         ρ^R = R⟦λ⟧ t ρ^R $ λ inc u^R → lemma t (𝓔^R‿∙ (𝓔^R‿wk inc ρ^R) u^R)
  lemma `⟨⟩            ρ^R = R⟦⟨⟩⟧ ρ^R
  lemma `tt            ρ^R = R⟦tt⟧ ρ^R
  lemma `ff            ρ^R = R⟦ff⟧ ρ^R
  lemma (`ifte b l r)  ρ^R = R⟦ifte⟧ b l r ρ^R (lemma b ρ^R) (lemma l ρ^R) (lemma r ρ^R)

record SyntacticFusable
  {ℓ^EA ℓ^EB ℓ^EC ℓ^REBC ℓ^RE : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} (synA : Syntactic 𝓔^A)
  (synB : Syntactic 𝓔^B)
  (synC : Syntactic 𝓔^C)
  (𝓔^R‿BC : {Γ : Con} {σ : ty} (e^B : 𝓔^B Γ σ) (e^C : 𝓔^C Γ σ) → Set ℓ^REBC)
  (𝓔^R : {Θ Δ Γ : Con} (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Θ [ 𝓔^B ] Δ) (ρ^C : Θ [ 𝓔^C ] Γ) → Set ℓ^RE)
  : Set (ℓ^RE ⊔ ℓ^REBC ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA)
  where
  module Syn^A = Syntactic synA
  module Syn^B = Syntactic synB
  module Syn^C = Syntactic synC
  field
    𝓔^R‿∙ : ({Γ Δ Θ : Con} {σ : ty} {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ}
               {u^B : 𝓔^B Θ σ} {u^C : 𝓔^C Θ σ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) (u^R : 𝓔^R‿BC u^B u^C) →
               𝓔^R (wk[ Syn^A.wk ] (step refl) ρ^A `∙ Syn^A.embed zero)
                      (ρ^B `∙ u^B)
                      (ρ^C `∙ u^C))
    𝓔^R‿wk : {Γ Δ Θ E : Con} (inc : Θ ⊆ E)
               {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ} (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
               𝓔^R ρ^A(wk[ Syn^B.wk ] inc ρ^B) (wk[ Syn^C.wk ] inc ρ^C)
    R⟦var⟧  : {Γ Δ Θ : Con} {σ : ty} (v : σ ∈ Γ) {ρ^A : Δ [ 𝓔^A ] Γ} {ρ^B : Θ [ 𝓔^B ] Δ} {ρ^C : Θ [ 𝓔^C ] Γ}
              (ρ^R : 𝓔^R ρ^A ρ^B ρ^C) →
              syntactic synB ⊨⟦ syntactic synA ⊨⟦ `var v ⟧ ρ^A ⟧ ρ^B ≡ syntactic synC ⊨⟦ `var v ⟧ ρ^C
\end{code}
%<*fusion-embed>
\begin{code}
    embed^BC : {Γ : Con} {σ : ty} → 𝓔^R‿BC  {Γ ∙ σ} (Syn^B.embed zero) (Syn^C.embed zero)
\end{code}
%</fusion-embed>
%<*syntactic-fusion>
\begin{code}
syntacticFusable :  {ℓ^EA ℓ^EB ℓ^EC ℓ^RE ℓ^REBC : Level} {𝓔^A : (Γ : Con) (σ : ty) → Set ℓ^EA} {𝓔^B : (Γ : Con) (σ : ty) → Set ℓ^EB} {𝓔^C : (Γ : Con) (σ : ty) → Set ℓ^EC} {syn^A : Syntactic 𝓔^A} {syn^B : Syntactic 𝓔^B} {syn^C : Syntactic 𝓔^C} {𝓔^R‿BC : {Γ : Con} {σ : ty} (e^B : 𝓔^B Γ σ) (e^C : 𝓔^C Γ σ) → Set ℓ^REBC} {𝓔^R : {Θ Δ Γ : Con} (ρ^A : Δ [ 𝓔^A ] Γ) (ρ^B : Θ [ 𝓔^B ] Δ) (ρ^C : Θ [ 𝓔^C ] Γ) → Set ℓ^RE} (syn^R : SyntacticFusable syn^A syn^B syn^C 𝓔^R‿BC 𝓔^R) →
  Fusable (syntactic syn^A) (syntactic syn^B) (syntactic syn^C) 𝓔^R‿BC 𝓔^R _≡_
\end{code}
%</syntactic-fusion>
\begin{code}

syntacticFusable synF =
  let open SyntacticFusable synF in
  record
    { reify^A    = id
    ; 𝓔^R‿∙   = 𝓔^R‿∙
    ; 𝓔^R‿wk  = 𝓔^R‿wk
    ; R⟦var⟧    = R⟦var⟧
    ; R⟦$⟧      = λ f t ρ^R → PEq.cong₂ _`$_
    ; R⟦λ⟧      = λ t ρ^R r → PEq.cong `λ (r (step refl) embed^BC)
    ; R⟦⟨⟩⟧     = λ ρ^R → PEq.refl
    ; R⟦tt⟧     = λ ρ^R → PEq.refl
    ; R⟦ff⟧     = λ ρ^R → PEq.refl
    ; R⟦ifte⟧   = λ b l r ρ^R eqb eql → PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ eqb eql)
    }

`var-inj : {Γ : Con} {σ : ty} {pr₁ pr₂ : σ ∈ Γ} (eq : (Γ ⊢ σ ∋ `var pr₁) ≡ `var pr₂) → pr₁ ≡ pr₂
`var-inj PEq.refl = PEq.refl
\end{code}
%<*fusion-renren>
\begin{code}
RenamingFusable :
  SyntacticFusable  syntacticRenaming syntacticRenaming syntacticRenaming
                    _≡_ (λ ρ^A ρ^B ρ^C → ∀ σ pr → lookup (trans ρ^A ρ^B) pr ≡ lookup ρ^C pr)
RenamingFusable = record
  { 𝓔^R‿∙     = λ ρ^R eq → [ eq , ρ^R ]
  ; 𝓔^R‿wk    = λ inc ρ^R σ pr → PEq.cong (lookup inc) (ρ^R σ pr)
  ; R⟦var⟧    = λ v ρ^R → PEq.cong `var (ρ^R _ v)
  ; embed^BC  = PEq.refl }
\end{code}
%</fusion-renren>
%<*fusion-rensub>
\begin{code}
RenamingSubstitutionFusable :
  SyntacticFusable syntacticRenaming syntacticSubstitution syntacticSubstitution
  _≡_ (λ ρ^A ρ^B ρ^C → ∀ σ pr → lookup ρ^B (lookup ρ^A pr) ≡ lookup ρ^C pr)
\end{code}
%</fusion-rensub>
\begin{code}
RenamingSubstitutionFusable =
  record { 𝓔^R‿∙   = λ ρ^R eq → [ eq , ρ^R ]
         ; 𝓔^R‿wk  = λ inc ρ^R σ pr → PEq.cong (λ t → Renaming ⊨⟦ t ⟧ inc) (ρ^R σ pr)
         ; R⟦var⟧    = λ v ρ^R → ρ^R _ v
         ; embed^BC   = PEq.refl }
\end{code}
%<*fusion-subren>
\begin{code}
SubstitutionRenamingFusable :
  SyntacticFusable syntacticSubstitution syntacticRenaming syntacticSubstitution
  (λ v t → `var v ≡ t) (λ ρ^A ρ^B ρ^C → ∀ σ pr → Renaming ⊨⟦ lookup ρ^A pr ⟧ ρ^B ≡ lookup ρ^C pr)
\end{code}
%</fusion-subren>
\begin{code}

SubstitutionRenamingFusable =
  let module RenRen = Fusion (syntacticFusable RenamingFusable) in
  record { 𝓔^R‿∙   = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} ρ^R eq → [ eq , (λ σ pr →
                         PEq.trans (RenRen.lemma (lookup ρ^A pr) (λ _ _ → PEq.refl))
                                   (ρ^R σ pr)) ]
         ; 𝓔^R‿wk  = λ inc {ρ^A} {ρ^B} {ρ^C} ρ^R σ pr →
                         PEq.trans (PEq.sym (RenRen.lemma (lookup ρ^A pr) (λ _ _ → PEq.refl)))
                                   (PEq.cong (λ t → Renaming ⊨⟦ t ⟧ inc) (ρ^R σ pr))
         ; R⟦var⟧    = λ v ρ^R → ρ^R _ v
         ; embed^BC   = PEq.refl }
\end{code}
%<*fusion-subsub>
\begin{code}
SubstitutionFusable :
  SyntacticFusable syntacticSubstitution syntacticSubstitution syntacticSubstitution
  _≡_ (λ ρ^A ρ^B ρ^C → ∀ σ pr → Substitution ⊨⟦ lookup ρ^A pr ⟧ ρ^B ≡ lookup ρ^C pr)
\end{code}
%</fusion-subsub>
\begin{code}

SubstitutionFusable =
  let module RenSubst = Fusion (syntacticFusable RenamingSubstitutionFusable)
      module SubstRen = Fusion (syntacticFusable SubstitutionRenamingFusable) in
  record { 𝓔^R‿∙   = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} ρ^R eq → [ eq , (λ σ pr →
                         PEq.trans (RenSubst.lemma (lookup ρ^A pr) (λ _ _ → PEq.refl))
                                   (ρ^R σ pr)) ]
         ; 𝓔^R‿wk  = λ inc {ρ^A} {ρ^B} {ρ^C} ρ^R σ pr →
                         PEq.trans (PEq.sym (SubstRen.lemma (lookup ρ^A pr) (λ _ _ → PEq.refl)))
                                   (PEq.cong (λ t → Renaming ⊨⟦ t ⟧ inc) (ρ^R σ pr))
         ; R⟦var⟧    = λ v ρ^R → ρ^R _ v
         ; embed^BC   = PEq.refl }

ifteRenNorm :
      {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      {ρ^A : Δ [ flip _∈_ ] Γ} {ρ^B : Θ [ _⊨^βιξη_ ] Δ}
      {ρ^C : Θ [ _⊨^βιξη_ ] Γ} →
      (ρ^R : (σ : ty) (pr : σ ∈ Γ) → EQREL Θ σ (lookup ρ^B (lookup ρ^A pr)) (lookup ρ^C pr)) →
      Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ b ⟧ ρ^A) ⟧ ρ^B ≡
      Normalise^βιξη ⊨⟦ b ⟧ ρ^C →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ l ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ l ⟧ ρ^C) →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ r ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ r ⟧ ρ^C) →
      EQREL Θ σ
      (Normalise^βιξη ⊨⟦ id (Renaming ⊨⟦ `ifte b l r ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρ^C)
ifteRenNorm b l r {ρ^A} {ρ^B} {ρ^C} ρ^R eqb eql eqr
  with Normalise^βιξη ⊨⟦ Renaming ⊨⟦ b ⟧ ρ^A ⟧ ρ^B
     | Normalise^βιξη ⊨⟦ b ⟧ ρ^C
ifteRenNorm b l r ρ^R PEq.refl eql eqr | `embed _ t | `embed _ .t =
  reflect^EQREL _ (PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ PEq.refl (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteRenNorm b l r ρ^R () eql eqr | `embed _ t | `tt
ifteRenNorm b l r ρ^R () eql eqr | `embed _ t | `ff
ifteRenNorm b l r ρ^R () eql eqr | `tt | `embed _ t
ifteRenNorm b l r ρ^R PEq.refl eql eqr | `tt | `tt = eql
ifteRenNorm b l r ρ^R () eql eqr | `tt | `ff
ifteRenNorm b l r ρ^R () eql eqr | `ff | `embed _ t
ifteRenNorm b l r ρ^R () eql eqr | `ff | `tt
ifteRenNorm b l r ρ^R PEq.refl eql eqr | `ff | `ff = eqr

\end{code}
%<*fusion-rennorm>
\begin{code}
RenamingNormaliseFusable : Fusable Renaming Normalise^βιξη Normalise^βιξη (EQREL _ _)
  (λ ρ^A ρ^B ρ^C → ∀ σ pr → EQREL _ σ (lookup ρ^B (lookup ρ^A pr)) (lookup ρ^C pr)) (EQREL _ _)
\end{code}
%</fusion-rennorm>
\begin{code}

RenamingNormaliseFusable =
  record
    { reify^A   = id
    ; 𝓔^R‿∙  = λ ρ^R u^R → [ u^R , ρ^R ]
    ; 𝓔^R‿wk = λ inc ρ^R → λ σ pr → wk^EQREL σ inc (ρ^R σ pr)
    ; R⟦var⟧   = λ v ρ^R → ρ^R _ v
    ; R⟦$⟧     = λ _ _ _ r → r refl
    ; R⟦λ⟧     = λ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ → ⟨⟩
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦ifte⟧  = ifteRenNorm
    }


ifteSubstNorm :
     {Γ Δ Θ : Con} {σ : ty} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ)
      {ρ^A : Δ [ _⊢_ ] Γ} {ρ^B : Θ [ _⊨^βιξη_ ] Δ}
      {ρ^C : Θ [ _⊨^βιξη_ ] Γ} →
      (`∀[ EQREL _ _ ] ρ^B ρ^B) ×
      ((σ₁ : ty) (pr : σ₁ ∈ Γ) {Θ₁ : Con} (inc : Θ ⊆ Θ₁) →
       EQREL Θ₁ σ₁
       (Normalise^βιξη ⊨⟦ lookup ρ^A pr ⟧
        (pack $ λ pr₁ → wk^βιξη _ inc $ lookup ρ^B pr₁))
       (wk^βιξη σ₁ inc $ lookup ρ^C pr))
      ×
      ((σ₁ : ty) (pr : σ₁ ∈ Γ) →
       EQREL Θ σ₁ (Normalise^βιξη ⊨⟦ lookup ρ^A  pr ⟧ ρ^B) (lookup ρ^C pr)) →
      Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ b ⟧ ρ^A) ⟧ ρ^B ≡
      Normalise^βιξη ⊨⟦ b ⟧ ρ^C →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ l ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ l ⟧ ρ^C) →
      EQREL Θ σ (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ r ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ r ⟧ ρ^C) →
      EQREL Θ σ
      (Normalise^βιξη ⊨⟦ id (Substitution ⊨⟦ `ifte b l r ⟧ ρ^A) ⟧ ρ^B)
      (Normalise^βιξη ⊨⟦ `ifte b l r ⟧ ρ^C)
ifteSubstNorm b l r {ρ^A} {ρ^B} {ρ^C} ρ^R eqb eql eqr
  with Normalise^βιξη ⊨⟦ Substitution ⊨⟦ b ⟧ ρ^A ⟧ ρ^B
     | Normalise^βιξη ⊨⟦ b ⟧ ρ^C
ifteSubstNorm b l r ρ^R PEq.refl eql eqr | `embed _ t | `embed _ .t =
  reflect^EQREL _ (PEq.cong₂ (uncurry `ifte) (PEq.cong₂ _,_ PEq.refl (reify^EQREL _ eql)) (reify^EQREL _ eqr))
ifteSubstNorm b l r ρ^R () eql eqr | `embed _ t | `tt
ifteSubstNorm b l r ρ^R () eql eqr | `embed _ t | `ff
ifteSubstNorm b l r ρ^R () eql eqr | `tt | `embed _ t
ifteSubstNorm b l r ρ^R PEq.refl eql eqr | `tt | `tt = eql
ifteSubstNorm b l r ρ^R () eql eqr | `tt | `ff
ifteSubstNorm b l r ρ^R () eql eqr | `ff | `embed _ t
ifteSubstNorm b l r ρ^R () eql eqr | `ff | `tt
ifteSubstNorm b l r ρ^R PEq.refl eql eqr | `ff | `ff = eqr

wk-refl : {Γ : Con} (σ : ty) {T U : Γ ⊨^βιξη σ} →
          EQREL Γ σ T U → EQREL Γ σ (wk^βιξη σ refl T) U
wk-refl `Unit     eq = ⟨⟩
wk-refl `Bool     eq = PEq.trans (wk^nf-refl _) eq
wk-refl (σ `→ τ)  eq = eq

wk^2 : {Θ Δ Γ : Con} (σ : ty) (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ) {T U : Γ ⊨^βιξη σ} →
       EQREL Γ σ T U → EQREL Θ σ (wk^βιξη σ inc₂ $ wk^βιξη σ inc₁ T) (wk^βιξη σ (trans inc₁ inc₂) U)
wk^2 `Unit     inc₁ inc₂ eq = ⟨⟩
wk^2 `Bool     inc₁ inc₂ eq = PEq.trans (wk^nf-trans inc₁ inc₂ _) (PEq.cong (wk^nf (trans inc₁ inc₂)) eq)
wk^2 (σ `→ τ)  inc₁ inc₂ eq = λ inc₃ → eq (trans inc₁ $ trans inc₂ inc₃)


\end{code}
%<*fusion-subnorm>
\begin{code}
SubstitutionNormaliseFusable : Fusable  Substitution Normalise^βιξη Normalise^βιξη
  (EQREL _ _)
  (λ ρ^A ρ^B ρ^C → `∀[ EQREL _ _ ] ρ^B ρ^B
                 × ((σ : ty) (pr : σ ∈ _) {Θ : Con} (inc : _ ⊆ Θ) →
                         EQREL Θ σ (Normalise^βιξη ⊨⟦ lookup ρ^A pr ⟧ (pack $ λ pr → wk^βιξη _ inc $ lookup ρ^B pr))
                                   (wk^βιξη σ inc $ lookup ρ^C pr))
                 × ((σ : ty) (pr : σ ∈ _) → EQREL _ σ (Normalise^βιξη ⊨⟦ lookup ρ^A pr ⟧ ρ^B) (lookup ρ^C pr)))
  (EQREL _ _)
\end{code}
%</fusion-subnorm>
\begin{code}

SubstitutionNormaliseFusable =
  let module RenNorm = Fusion RenamingNormaliseFusable
      module EqNorm  = Synchronised SynchronisableNormalise in
  record
    { reify^A   = id
    ; 𝓔^R‿∙  = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} ρ^R u^R →
                     (proj₁ ρ^R ∙^R reflEQREL _ u^R)
                   , [ (λ {Θ} inc → wk^EQREL _ inc u^R)
                     , (λ σ pr {Θ} inc →
                       transEQREL σ (RenNorm.lemma (lookup ρ^A pr)
                                                    (λ σ pr → wk^EQREL σ inc (lookup^R (proj₁ ρ^R) pr)))
                                    ((proj₁ ∘ proj₂) ρ^R σ pr inc)) ]
                     , [ u^R , (λ σ pr → transEQREL σ (RenNorm.lemma (lookup ρ^A pr) (λ _ → lookup^R $ proj₁ ρ^R))
                                          ((proj₂ ∘ proj₂) ρ^R σ pr)) ]
    ; 𝓔^R‿wk = λ inc {ρ^A} ρ^R →
                            (pack^R $ λ pr → wk^EQREL _ inc (lookup^R (proj₁ ρ^R) pr))
                          , (λ σ pr {Θ} inc′ →
                               transEQREL σ (EqNorm.lemma (lookup ρ^A pr)
                               (pack^R $ λ pr → transEQREL _ (wk^2 _ inc inc′ (lookup^R (proj₁ ρ^R) pr))
                                                      (wk^EQREL _ (trans inc inc′) (lookup^R (proj₁ ρ^R) pr))))
                               (transEQREL σ ((proj₁ ∘ proj₂) ρ^R σ pr (trans inc inc′))
                               (symEQREL σ (wk^2 σ inc inc′ (reflEQREL σ (symEQREL σ $ (proj₂ ∘ proj₂) ρ^R σ pr))))))
                          , (λ σ pr → (proj₁ ∘ proj₂) ρ^R σ pr inc)
    ; R⟦var⟧   = λ v ρ^R → (proj₂ ∘ proj₂) ρ^R _ v
    ; R⟦$⟧     = λ _ _ _ r → r refl
    ; R⟦λ⟧     = λ _ _ r → r
    ; R⟦⟨⟩⟧    = λ _ → ⟨⟩
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦ifte⟧  = ifteSubstNorm
    }

both : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} (eq : (A × B ∋ a₁ , b₁) ≡ (a₂ , b₂)) → a₁ ≡ a₂ × b₁ ≡ b₂
both PEq.refl = PEq.refl , PEq.refl

∷-inj : {A : Set} {a b : A} {as bs : ∞ (Stream A)} (eq : (Stream A ∋ a ∷ as) ≡ b ∷ bs) → a ≡ b × as ≡ bs
∷-inj PEq.refl = PEq.refl , PEq.refl

\end{code}
%<*fusion-renpretty>
\begin{code}
RenamingPrettyPrintingFusable : Fusable Renaming Printing Printing _≡_
  (λ ρ^A ρ^B → `∀[ _≡_ ] (trans ρ^A ρ^B))
  (λ p q → ∀ {names₁ names₂} → names₁ ≡ names₂ → runPrinter p names₁ ≡ runPrinter q names₂)
\end{code}
%</fusion-renpretty>
\begin{code}

RenamingPrettyPrintingFusable = record
  { reify^A   = id
  ; 𝓔^R‿∙   = λ {Γ} {Δ} {Θ} {σ} {ρ^A} {ρ^B} {ρ^C} {u^B} {u^C} ρ^R eq → pack^R $ (λ {σ} v → [_,_] {P = λ σ v → lookup (trans (step ρ^A `∙ zero) (ρ^B `∙ u^B)) v ≡ lookup (ρ^C `∙ u^C) v} eq (λ σ v → lookup^R ρ^R v) σ v)
  ; 𝓔^R‿wk  = λ _ ρ^R → pack^R $ PEq.cong (mkName ∘ runName) ∘ lookup^R ρ^R
  ; R⟦var⟧   = λ v ρ^R → PEq.cong₂ (λ n ns → runName n , ns) (lookup^R ρ^R v)
  ; R⟦λ⟧     = λ t ρ^R r → λ { {n₁ ∷ n₁s} {n₂ ∷ n₂s} eq →
                        let (neq   , nseq) = ∷-inj eq
                            (ihstr , ihns) = both (r (step refl) (PEq.cong mkName neq) (PEq.cong ♭ nseq))
                        in PEq.cong₂ _,_ (PEq.cong₂ (λ n str → "λ" ++ n ++ ". " ++ str) neq ihstr) ihns }
  ; R⟦$⟧     = λ f t {ρ^A} {ρ^B} {ρ^C} ρ^R ihf iht eq →
                        let (ihstrf , eq₁) = both (ihf eq)
                            (ihstrt , eq₂) = both (iht eq₁)
                        in PEq.cong₂ _,_ (PEq.cong₂ (λ strf strt → strf ++ " (" ++ strt ++ ")") ihstrf ihstrt) eq₂
  ; R⟦⟨⟩⟧    = λ _ → PEq.cong _
  ; R⟦tt⟧    = λ _ → PEq.cong _
  ; R⟦ff⟧    = λ _ → PEq.cong _
  ; R⟦ifte⟧  = λ b l r {ρ^A} {ρ^B} {ρ^C} ρ^R ihb ihl ihr eq →
                       let (ihstrb , eq₁) = both (ihb eq)
                           (ihstrl , eq₂) = both (ihl eq₁)
                           (ihstrr , eq₃) = both (ihr eq₂)
                       in PEq.cong₂ _,_ (PEq.cong₂ (λ strb strlr → "if (" ++ strb ++ ") then (" ++ strlr)
                                        ihstrb (PEq.cong₂ (λ strl strr → strl ++ ") else (" ++ strr ++ ")")
                                        ihstrl ihstrr)) eq₃ }

tailComm : (Δ Γ : Con) {names : Stream String} →
           tail (proj₂ (nameContext Δ Γ names)) ≡ proj₂ (nameContext Δ Γ (tail names))
tailComm Δ ε        = PEq.refl
tailComm Δ (Γ ∙ _)  = PEq.cong tail (tailComm Δ Γ)

proof : (Δ Γ : Con) {names : Stream String} → proj₂ (nameContext Δ Γ names) ≡ Stream.drop (size Γ) names
proof Δ ε       = PEq.refl
proof Δ (Γ ∙ _) = λ { {_ ∷ names} → PEq.trans (tailComm Δ Γ) (proof Δ Γ) }

\end{code}
%<*pretty-renaming>
\begin{code}
PrettyRenaming : {Γ : Con} {σ : ty} (t : ε ⊢ σ) (inc : ε ⊆ Γ) →
  print (wk^⊢ inc t) ≡ proj₁ (runPrinter (Printing ⊨⟦ t ⟧ `ε) $ Stream.drop (size Γ) names)
PrettyRenaming {Γ} t inc = PEq.cong proj₁ $ lemma t (pack^R $ λ ()) $ proof Γ Γ
  where open Fusion RenamingPrettyPrintingFusable
\end{code}
%</pretty-renaming>
