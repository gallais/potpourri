module linear.Context where

open import Function
open import Data.Nat as ℕ
open import Data.Fin
open import Data.Vec as V hiding (_++_)

open import linear.Type
open import linear.Scope as Sc hiding (Mergey ; copys ; inserts)
open import Relation.Binary.PropositionalEquality

Context : ℕ → Set
Context = Vec Type

_++_ = V._++_

-- Induction principle
induction :
  (P : {n : ℕ} → Context n → Set)
  (pε : P [])
  (p∷ : {n : ℕ} (a : Type) (Γ : Context n) → P Γ → P (a ∷ Γ)) →
  {n : ℕ} (Γ : Context n) → P Γ
induction P pε p∷ []      = pε
induction P pε p∷ (a ∷ Γ) = p∷ a Γ (induction P pε p∷ Γ)

data Mergey : {k l : ℕ} (m : Sc.Mergey k l) → Set where
  finish : {k : ℕ} → Mergey (finish {k})
  copy   : {k l : ℕ} {m : Sc.Mergey k l} → Mergey m → Mergey (copy m)
  insert : {k l : ℕ} {m : Sc.Mergey k l} → Type → Mergey m → Mergey (insert m)

copys : (o : ℕ) {k l : ℕ} {m : Sc.Mergey k l} (M : Mergey m) → Mergey (Sc.copys o m)
copys zero    M = M
copys (suc o) M = copy (copys o M)

inserts : {o k l : ℕ} (O : Context o) {m : Sc.Mergey k l} →
          Mergey m → Mergey (Sc.inserts o m)
inserts []      M = M
inserts (σ ∷ O) M = insert σ (inserts O M)

infixl 4 _⋈_
_⋈_ : {k l : ℕ} (Γ : Context k) {m : Sc.Mergey k l} (M : Mergey m) → Context l
Γ     ⋈ finish     = Γ
a ∷ Γ ⋈ copy M     = a ∷ (Γ ⋈ M)
Γ     ⋈ insert a M = a ∷ (Γ ⋈ M)

++copys-elim : {k l o : ℕ} {m : Sc.Mergey k l} (P : Context (o ℕ.+ l) → Set)
               (δ : Context o) (γ : Context k) (M : Mergey m) →
               P ((δ ++ γ) ⋈ copys o M) → P (δ ++ (γ ⋈ M))
++copys-elim P []      γ M p = p
++copys-elim P (a ∷ δ) γ M p = ++copys-elim (P ∘ (a ∷_)) δ γ M p
