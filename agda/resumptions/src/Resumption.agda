{-# OPTIONS --guardedness #-}

module Resumption where

open import Level using (Level; 0ℓ; suc; _⊔_)

open import Algebra.Definitions.RawMagma

open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product.Base using (∃; _×_; _,_; uncurry)

open import Function.Base using (_∘′_)

open import Relation.Binary.Bundles using (Preorder)
open import Relation.Unary using (Pred; IUniversal; _⇒_)



variable
  a b c : Level

module Presheaf {a r e} (P : Preorder a e r) where

  open Preorder P renaming (Carrier to A)
  open import Relation.Unary.Closure.Base _≲_

  record Psh (ℓ : Level) : Set (a ⊔ r ⊔ suc ℓ) where
    field
      family : A → Set ℓ
      action : ∀[ family ⇒ □ family ]
  open Psh public

module Definition {a r e} (P : Preorder a e r) where

  open Preorder P renaming (Carrier to A)
  open import Relation.Unary.Closure.Base _≲_
  open Presheaf P public

  data Res (B : Psh b) (x : A) : Set (a ⊔ r ⊔ b)

  record Thk (B : Psh b) (x : A)  : Set (a ⊔ r ⊔ b) where
    coinductive
    field force : □ (Res B) x
  open Thk public

  data Res B x where
    completed : family B x → Res B x
    suspended : Thk B x → Res B x

  res : (B : Psh b) → Psh (a ⊔ r ⊔ b)
  res B .family = Res B
  res B .action (completed r) x≲y = completed (B .action r x≲y)
  res B .action (suspended t) x≲y = t .force x≲y

  finalise : {B : Psh b} → ∀[ Res B ⇒ Maybe ∘′ (B .family) ]
  finalise (completed r) = just r
  finalise (suspended _) = nothing

  resume : {B : Psh b} → ∀[ Res B ⇒ □ (Res B) ]
  resume r x≲y = res _ .action r x≲y

  module _ {B : Psh b} {C : Psh c}
    (f : A → A)
    (f≲-compat : ∀ {x y} → f x ≲ y → ∃ λ x′ → y ≈ f x′ × x ≲ x′)
    (F : ∀ {x} → B .family x → ∀ {y} → y ≈ f x → C .family y)
    where

    mapI  : ∀ {x} → Res B x → ∀ {y} → y ≈ f x → Res C y
    mapI∞ : ∀ {x} → Thk B x → ∀ {y} → y ≈ f x → Thk C y

    mapI (completed v) y≈fx = completed (F v y≈fx)
    mapI (suspended t) y≈fx = suspended (mapI∞ t y≈fx)

    mapI∞ t y≈fx .force fx≲y =
      let (x′ , y≈fx′ , x≲x′) = f≲-compat (trans (reflexive (Eq.sym y≈fx)) fx≲y) in
      let r = t .force x≲x′ in mapI r y≈fx′

module Example where

  open import Data.List.Base as List using (List; []; _∷_)
  open import Data.List.Properties using (++-monoid)
  open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_; head; tail; _++ᵖ_)
  open import Data.List.Relation.Binary.Prefix.Propositional.Properties
  open import Data.List.Relation.Unary.Any using (Any; here; there)
  open import Data.Nat.Base using (ℕ)
  open import Data.Nat.Properties using (_≟_)
  open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)

  open import Relation.Nullary.Decidable as Dec using (Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Function.Base using (_∘′_)

  open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

  open import Algebra.Properties.Monoid.Divisibility (++-monoid ℕ) using (_∣ˡ_; ∣ˡ-preorder)
  open Definition ∣ˡ-preorder


  decPrefix : (pref : List ℕ) → Psh 0ℓ
  decPrefix prefix .family = λ w → Prefix _≡_ prefix w ⊎ Any (uncurry _≢_) (List.zip prefix w)
  decPrefix prefix .action (inj₁ prf) (suffix , refl) = inj₁ (prf ++ᵖ suffix)
  decPrefix prefix .action (inj₂ prf) (suffix , refl) = inj₂ (go _ prefix _ suffix prf) where

    go : ∀ P xs ys zs → Any P (List.zip xs ys) → Any P (List.zip xs (ys List.++ zs))
    go P (x ∷ xs) (x₁ ∷ ys) zs (here px) = here px
    go P (x ∷ xs) (x₁ ∷ ys) zs (there prf) = there (go P xs ys zs prf)

  isPrefix : ∀ (pref val : List ℕ) → Res (decPrefix pref) val
  isPrefix∞ : ∀ (pref : List ℕ) → Thk (decPrefix pref) []

  isPrefix [] val = completed (inj₁ [])
  isPrefix pref [] = suspended (isPrefix∞ pref)
  isPrefix (x ∷ pref) (y ∷ val) with x ≟ y
  ... | no x≢y = completed (inj₂ (here x≢y))
  ... | yes refl
    = mapI
      (x ∷_)
      (λ where (_ , refl) → _ , refl , _ , refl)
      (λ where dec refl → Sum.map (refl ∷_) there dec)
      (isPrefix pref val)
      refl

  isPrefix∞ pref .force (val , refl) = isPrefix pref val

  testT : Res (decPrefix (1 ∷ 2 ∷ 3 ∷ [])) (1 ∷ 2 ∷ [])
  testT = isPrefix _ _

  _ : finalise testT ≡ nothing
  _ = refl

  testS : Res (decPrefix (1 ∷ 2 ∷ 3 ∷ [])) (1 ∷ 2 ∷ 3 ∷ [])
  testS = resume testT (3 ∷ [] , refl)

  _ : finalise testS ≡ just (inj₁ (refl ∷ refl ∷ refl ∷ []))
  _ = refl

  testF : Res (decPrefix (1 ∷ 2 ∷ 3 ∷ [])) (1 ∷ 2 ∷ 4 ∷ [])
  testF = resume testT (4 ∷ [] , refl)

  _ : finalise testF ≡ just (inj₂ (there (there (here _))))
  _ = refl
