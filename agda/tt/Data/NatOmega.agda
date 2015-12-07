module tt.Data.NatOmega where

open import Data.Nat as ℕ using (ℕ)
open import Function hiding (_⟨_⟩_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

infix 10 ↑_
data ℕω : Set where
  ↑_ : (l : ℕ) → ℕω
  ω  : ℕω

infix 4 _<_
data _<_ : (m n : ℕω) → Set where
  ↑_   : {k l : ℕ} (lt : k ℕ.< l) → ↑ k < ↑ l 
  ↑_<ω : (l : ℕ) → ↑ l < ω

↑<↑-inv : {k l : ℕ} → ↑ k < ↑ l → k ℕ.< l
↑<↑-inv (↑ lt ) = lt

⇑-inj : {k l : ℕ} → (ℕω ∋ ↑ k) ≡ ↑ l → k ≡ l
⇑-inj refl = refl

infix 4 _<?_ _≟_
_<?_ : (m n : ℕω) → Dec (m < n)
ω <? _         = no λ ()
↑ k <? ω     = yes $ ↑ k <ω
↑ k <? ↑ l with ℕ.suc k ℕ.≤? l
... | yes p = yes (↑ p)
... | no ¬p = no (¬p ∘ ↑<↑-inv)

_≟_ : (m n : ℕω) → Dec (m ≡ n)
ω   ≟ ω   = yes refl
↑ k ≟ ↑ l with k ℕ.≟ l
... | yes p = yes $ cong ↑_ p
... | no ¬p = no (¬p ∘ ⇑-inj)

↑ k ≟ ω   = no λ ()
ω   ≟ ↑ l = no λ ()
