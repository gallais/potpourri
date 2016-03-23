module linear.Usage where

open import Data.Nat as ℕ
open import Data.Fin
open import Data.Vec hiding ([_])
open import Function

open import linear.Type
open import linear.Scope as Sc hiding (Mergey ; copys)
open import linear.Context as C hiding (Mergey ; _⋈_ ; copys ; Holey ; _⇐_)

data Usage : (a : Type) → Set where
  [_] : (a : Type) → Usage a
  ]_[ : (a : Type) → Usage a

infixl 5 _∙_ _∷_
data Usages : {n : ℕ} (γ : Context n) → Set where
  []  : Usages []
  _∷_ : {n : ℕ} {γ : Context n} {a : Type} → Usage a → Usages γ → Usages (a ∷ γ)

infix 1 _⊢_∈[_]⊠_
data _⊢_∈[_]⊠_ : {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) (a : Type) (Δ : Usages γ) → Set where
  z : {n : ℕ} {γ : Context n} {Γ : Usages γ} {a : Type} → [ a ] ∷ Γ ⊢ zero ∈[ a ]⊠ ] a [ ∷ Γ
  s_ : {n : ℕ} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ} {a b : Type} {u : Usage b} →
       Γ ⊢ k ∈[ a ]⊠ Δ → u ∷ Γ ⊢ suc k ∈[ a ]⊠ u ∷ Δ

data Holey {m : ℕ} : {n : ℕ} (h : C.Holey m n) → Set where
  []  : Holey []
  _∷_ : {n : ℕ} {h : C.Holey m n} {a : Type} → Usage a → Holey h → Holey (a ∷ h)
  _∙_ : {n o : ℕ} {g : C.Holey m n} {h : C.Holey n o} → Holey g → Holey h → Holey (g ∙ h)

infixr 4 _⇐_
_⇐_ : {m n : ℕ} {h : C.Holey m n} (H : Holey h) {γ : Context m} → Usages γ → Usages (h C.⇐ γ)
[]    ⇐ Γ = Γ
a ∷ h ⇐ Γ = a ∷ (h ⇐ Γ)
g ∙ h ⇐ Γ = h ⇐ (g ⇐ Γ)


[[_]] : {m n : ℕ} (δ : Context n) → Holey {m} (δ ++)
[[ δ ]] = induction (Holey ∘ _++) [] (λ a _ → [ a ] ∷_) δ

]]_[[ : {m n : ℕ} (δ : Context n) → Holey {m} (δ ++)
]] δ [[ = induction (Holey ∘ _++) [] (λ a _ → ] a [ ∷_) δ

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
