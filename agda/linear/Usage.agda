module linear.Usage where

open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_])

open import linear.Type
open import linear.Scope as Sc hiding (Mergey)
open import linear.Context as C hiding (Mergey ; _⋈_)

data Usage : (a : Type) → Set where
  [_] : (a : Type) → Usage a
  ]_[ : (a : Type) → Usage a

infixl 10 _∙_
data Usages : {n : ℕ} (γ : Context n) → Set where
  []  : Usages []
  _∷_ : {n : ℕ} {γ : Context n} {a : Type} → Usage a → Usages γ → Usages (a ∷ γ)

infix 1 _⊢_∈[_]⊠_
data _⊢_∈[_]⊠_ : {n : ℕ} {γ : Context n} (Γ : Usages γ) (k : Fin n) (a : Type) (Δ : Usages γ) → Set where
  z : {n : ℕ} {γ : Context n} {Γ : Usages γ} {a : Type} → [ a ] ∷ Γ ⊢ zero ∈[ a ]⊠ ] a [ ∷ Γ
  s_ : {n : ℕ} {γ : Context n} {k : Fin n} {Γ Δ : Usages γ} {a b : Type} {u : Usage b} →
       Γ ⊢ k ∈[ a ]⊠ Δ → u ∷ Γ ⊢ suc k ∈[ a ]⊠ u ∷ Δ

data HoleyUsages {m : ℕ} : {n : ℕ} (h : Holey m n) → Set where
  []  : HoleyUsages []
  _∷_ : {n : ℕ} {h : Holey m n} {a : Type} → HoleyUsages h → Usage a → HoleyUsages (a ∷ h)
  _∙_ : {n o : ℕ} {g : Holey m n} {h : Holey n o} → HoleyUsages g → HoleyUsages h → HoleyUsages (g ∙ h)

[[_]]++_ : {m n : ℕ} {γ : Context m} (δ : Context n) (Γ : Usages γ) → Usages (δ ++ γ)
[[ δ ]]++ Γ = induction (λ δ → Usages (δ ++ _)) Γ (λ a Γ → [ a ] ∷_) δ

]]_[[++_ : {m n : ℕ} {γ : Context m} (δ : Context n) (Γ : Usages γ) → Usages (δ ++ γ)
]] δ [[++ Γ = induction (λ δ → Usages (δ ++ _)) Γ (λ a Γ → ] a [ ∷_) δ

data Mergey : {k l : ℕ} {m : Sc.Mergey k l} (M : C.Mergey m) → Set where
  finish : {k : ℕ} → Mergey (finish {k})
  copy   : {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} (𝓜 : Mergey M) → Mergey (copy M)
  insert : {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} {a : Type}
           (A : Usage a) (𝓜 : Mergey M) → Mergey (insert a M)

infixl 4 _⋈_
_⋈_ : {k l : ℕ} {γ : Context k} {m : Sc.Mergey k l} {M : C.Mergey m}
      (Γ : Usages γ) (𝓜 : Mergey M) → Usages (γ C.⋈ M)
Γ     ⋈ finish     = Γ
A ∷ Γ ⋈ copy M     = A ∷ (Γ ⋈ M)
Γ     ⋈ insert A M = A ∷ (Γ ⋈ M)
