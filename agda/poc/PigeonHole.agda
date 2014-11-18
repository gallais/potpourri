module PigeonHole where

open import Data.Empty
open import Data.Sum
open import Data.Nat
open import Data.List
open import Function

open import Relation.Binary.PropositionalEquality

-- membership predicate
infix 5 _∈_
data _∈_ {X : Set} (x : X) : (xs : List X) → Set where
  here! : {xs : List X} → x ∈ x ∷ xs
  there : {xs : List X} {y : X} (pr : x ∈ xs) → x ∈ y ∷ xs

x∈[] : {X : Set} {x : X} (pr : x ∈ []) → ⊥
x∈[] ()

x∈y∷ys : {X : Set} {x y : X} {ys : List X} {P : (x : X) (pr : x ∈ y ∷ ys) → Set}
         (phere! : P y here!) (pthere : (x : X) (pr : x ∈ ys) → P x (there pr))
         (pr : x ∈ y ∷ ys) → P x pr
x∈y∷ys phere! pthere here!      = phere!
x∈y∷ys phere! pthere (there pr) = pthere _ pr

remove : {X : Set} {x : X} (xs : List X) (pr : x ∈ xs) → List X
remove (_ ∷ xs) here!      = xs
remove (y ∷ xs) (there pr) = y ∷ remove xs pr

remove-length : {X : Set} {x : X} {xs : List X} (pr : x ∈ xs) → suc (length $ remove xs pr) ≡ length xs
remove-length here!      = refl
remove-length (there pr) = cong suc $ remove-length pr

remove-lemma : {X : Set} {x : X} {xs : List X} (pr : x ∈ xs) →
               {y : X} (pr′ : y ∈ xs) → x ≡ y ⊎ y ∈ remove xs pr
remove-lemma here!      here!       = inj₁ refl
remove-lemma (there pr) here!       = inj₂ here!
remove-lemma here!      (there pr′) = inj₂ pr′
remove-lemma (there pr) (there pr′) = [ inj₁ , inj₂ ∘ there ]′ (remove-lemma pr pr′)

remove-hyp : {X : Set} {y : X} {ys : List X} (pr : y ∈ ys) →
             (xs : List X) (hyp : (x : X) → x ∈ xs → x ∈ ys) →
             y ∈ xs ⊎ ((x : X) → x ∈ xs → x ∈ remove ys pr)
remove-hyp pr []       hyp = inj₂ $ λ _ → ⊥-elim ∘ x∈[]
remove-hyp pr (x ∷ xs) hyp with remove-hyp pr xs (λ x → hyp x ∘ there) | remove-lemma pr (hyp x here!)
...                        | inj₁ yin | _         = inj₁ $ there yin
...                        | inj₂ ih  | inj₂ xin  = inj₂ $ λ x′ → x∈y∷ys xin ih
remove-hyp pr (y ∷ xs) hyp | _        | inj₁ refl = inj₁ here!

data repeats {X : Set} : (xs : List X) → Set where
  this : {x : X} {xs : List X} (pr : x ∈ xs) → repeats $ x ∷ xs
  that : {x : X} {xs : List X} (pr : repeats xs) → repeats $ x ∷ xs

pigeonHole : {X : Set} (xs ys : List X)
             (hyp : (x : X) → x ∈ xs → x ∈ ys) →
             length ys < length xs → repeats xs
pigeonHole []       ys hyp ()
pigeonHole (x ∷ xs) ys hyp (s≤s len) with remove-hyp (hyp x here!) xs (λ x → hyp x ∘ there)
... | inj₁ pr   = this pr
... | inj₂ hyp′ = that $ pigeonHole xs (remove ys $ hyp x here!) hyp′ len′
  where len′ = subst (flip _≤_ $ length xs) (sym $ remove-length $ hyp x here!) len