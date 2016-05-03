module linear.Context.Pointwise where

open import Data.Nat
open import Data.Vec using ([] ; _∷_)
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_ ; cong₂ ; subst)

open import linear.Scope as Sc hiding (copys)
open import linear.Type
open import linear.Context as C hiding (_++_ ; copys)
open import linear.Usage hiding (_++_ ; copys)

data Context[_] (R : (σ τ : Type) → Set) : {k : ℕ} (γ δ : Context k) → Set where
  []  : Context[ R ] [] []
  _∷_ : {σ τ : Type} {k : ℕ} {γ δ : Context k} →
        R σ τ → Context[ R ] γ δ → Context[ R ] (σ ∷ γ) (τ ∷ δ)

_++_ : {R : (σ τ : Type) → Set} {k l : ℕ} {γ γ′ : Context k} {δ δ′ : Context l} →
       Context[ R ] γ γ′ → Context[ R ] δ δ′ → Context[ R ] (γ C.++ δ) (γ′ C.++ δ′)
[]       ++ ss = ss
(r ∷ rs) ++ ss = r ∷ (rs ++ ss)

refl : {k : ℕ} {γ : Context k} → Context[ _≡_ ] γ γ
refl {γ = []}    = []
refl {γ = σ ∷ γ} = PEq.refl ∷ refl

sym : {k : ℕ} {γ δ : Context k} → Context[ _≡_ ] γ δ → Context[ _≡_ ] δ γ
sym []         = []
sym (eq ∷ eqs) = PEq.sym eq ∷ sym eqs

trans : {k : ℕ} {γ δ θ : Context k} → Context[ _≡_ ] γ δ → Context[ _≡_ ] δ θ →
        Context[ _≡_ ] γ θ
trans []           []           = []
trans (eq₁ ∷ eqs₁) (eq₂ ∷ eqs₂) = PEq.trans eq₁ eq₂ ∷ trans eqs₁ eqs₂

copys : {k l o : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} {γ : Context k} (δ : Context o) →
        Context[ _≡_ ] (δ C.++ γ C.⋈ C.copys o M) (δ C.++ (γ C.⋈ M))
copys []      = refl
copys (σ ∷ δ) = PEq.refl ∷ copys δ
        
pointwiseEq : {k : ℕ} {γ δ : Context k} → Context[ _≡_ ] γ δ → γ ≡ δ
pointwiseEq []         = PEq.refl
pointwiseEq (eq ∷ eqs) = cong₂ (_∷_) eq $ pointwiseEq eqs

coerce :
  {k l : ℕ} {γ : Context l} {δ : Context k} {m : Sc.Mergey k l}
  (M : C.Mergey m) → Context[ _≡_ ] γ (δ C.⋈ M) → Usages γ → Usages (δ C.⋈ M)
coerce             finish       []         []      = []
coerce             finish       (eq ∷ eqs) (S ∷ Γ) = subst Usage eq S ∷ coerce finish eqs Γ
coerce             (insert σ M) (eq ∷ eqs) (S ∷ Γ) = subst Usage eq S ∷ coerce M eqs Γ
coerce {δ = σ ∷ δ} (copy M)     (eq ∷ eqs) (S ∷ Γ) = subst Usage eq S ∷ coerce M eqs Γ
