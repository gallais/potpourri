module linear.Usage where

open import Data.Nat as ℕ
open import Data.Fin
open import Data.Vec hiding ([_] ; _++_)
open import Function

open import linear.Type
open import linear.Scope as Sc hiding (Mergey ; copys)
open import linear.Context as C hiding (Mergey ; _⋈_ ; copys ; _++_ ; ++copys-elim)
open import Relation.Binary.PropositionalEquality

data Usage : (a : Type) → Set where
  [_] : (a : Type) → Usage a
  ]_[ : (a : Type) → Usage a

infixl 5 _∷_ -- _∙_
data Usages : {n : ℕ} (γ : Context n) → Set where
  []  : Usages []
  _∷_ : {n : ℕ} {γ : Context n} {a : Type} → Usage a → Usages γ → Usages (a ∷ γ)

infixr 4 _++_
_++_ : {m n : ℕ} {γ : Context m} {δ : Context n}
       (Γ : Usages γ) (Δ : Usages δ) → Usages (γ C.++ δ)
[]    ++ Δ = Δ
x ∷ Γ ++ Δ = x ∷ (Γ ++ Δ)

infix 1 _⊢_∈[_]⊠_
data _⊢_∈[_]⊠_ : {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) (a : Type) (Δ : Usages γ) → Set where
  z : {n : ℕ} {γ : Context n} {Γ : Usages γ} {a : Type} → [ a ] ∷ Γ ⊢ zero ∈[ a ]⊠ ] a [ ∷ Γ
  s_ : {n : ℕ} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ} {a b : Type} {u : Usage b} →
       Γ ⊢ k ∈[ a ]⊠ Δ → u ∷ Γ ⊢ suc k ∈[ a ]⊠ u ∷ Δ

{-
data Holey {m : ℕ} : {n : ℕ} (h : C.Holey m n) → Set where
  []  : Holey []
  _∷_ : {n : ℕ} {h : C.Holey m n} {a : Type} → Usage a → Holey h → Holey (a ∷ h)
  _∙_ : {n o : ℕ} {g : C.Holey m n} {h : C.Holey n o} → Holey g → Holey h → Holey (g ∙ h)

infixr 4 _⇐_
_⇐_ : {m n : ℕ} {h : C.Holey m n} (H : Holey h) {γ : Context m} → Usages γ → Usages (h C.⇐ γ)
[]    ⇐ Γ = Γ
a ∷ h ⇐ Γ = a ∷ (h ⇐ Γ)
g ∙ h ⇐ Γ = h ⇐ (g ⇐ Γ)
-}

[[_]] : {m  : ℕ} (δ : Context m) → Usages δ
[[ δ ]] = induction Usages [] (λ a _ → [ a ] ∷_) δ

]]_[[ : {m : ℕ} (δ : Context m) → Usages δ
]] δ [[ = induction Usages [] (λ a _ → ] a [ ∷_) δ

data Mergey : {k l : ℕ} {m : Sc.Mergey k l} (M : C.Mergey m) → Set where
  finish : {k : ℕ} → Mergey (finish {k})
  copy   : {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} (𝓜 : Mergey M) → Mergey (copy M)
  insert : {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} {a : Type}
           (A : Usage a) (𝓜 : Mergey M) → Mergey (insert a M)

copys : (o : ℕ) {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} → Mergey M → Mergey (C.copys o M)
copys zero    M = M
copys (suc o) M = copy (copys o M)

infixl 4 _⋈_
_⋈_ : {k l : ℕ} {γ : Context k} {m : Sc.Mergey k l} {M : C.Mergey m}
      (Γ : Usages γ) (𝓜 : Mergey M) → Usages (γ C.⋈ M)
Γ     ⋈ finish     = Γ
A ∷ Γ ⋈ copy M     = A ∷ (Γ ⋈ M)
Γ     ⋈ insert A M = A ∷ (Γ ⋈ M)


++copys-elim₂ :
  {k l o : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} {δ : Context o} {γ : Context k}
  (P : {γ : Context (o ℕ.+ l)} → Usages γ → Usages γ → Set)
  (Δ Δ′ : Usages δ) (Γ Γ′ : Usages γ) (𝓜 : Mergey M) →
  P ((Δ ++ Γ) ⋈ copys o 𝓜) ((Δ′ ++ Γ′) ⋈ copys o 𝓜) → P (Δ ++ (Γ ⋈ 𝓜)) (Δ′ ++ (Γ′ ⋈ 𝓜))
++copys-elim₂ P []      []        Γ Γ′ 𝓜 p = p
++copys-elim₂ P (A ∷ Δ) (A′ ∷ Δ′) Γ Γ′ 𝓜 p = ++copys-elim₂ (λ θ θ′ → P (A ∷ θ) (A′ ∷ θ′)) Δ Δ′ Γ Γ′ 𝓜 p
