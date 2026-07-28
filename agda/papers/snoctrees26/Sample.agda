-- Based on
-- Snoc Trees: Growing Trees From the Leaves
-- by Neil Ghani, Fredrik Nordvall Forsberg, Samuel Fish
-- https://fredriknf.com/papers/snoc_act2026.pdf

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; uncons)
open import Data.Maybe.Base using (Maybe; nothing; just; maybe′)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤)

open import Function.Base using (_∘′_; const)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable
  A B : Set
  T : A → Set

postulate
  R : Set → Set
  _>>=_  : R A → (A → R B) → R B
  return : A → R A

  D : Set → Set
  mapD     : (A → B) → D A → D B
  reindexD : (A → B) → D B → D A

mapR : (A → B) → R A → R B
mapR f = _>>= (return ∘′ f)

Sampling : Set → Set
Sampling A = D A → R A

postulate
  bool : Sampling Bool

record Iso (A B : Set) : Set where
  field
    fwd : A → B
    bwd : B → A
    .id₁ : ∀ a → bwd (fwd a) ≡ a
    .id₂ : ∀ b → fwd (bwd b) ≡ b
open Iso

seq : Sampling A → ((a : A) → Sampling (T a)) → Sampling (Σ A T)
seq sa st dat = do
  a ← sa (mapD proj₁ dat)
  mapR (a ,_) (st a (reindexD (a ,_) dat))

prod : Sampling A → Sampling B → Sampling (A × B)
prod sa sb = seq sa (const sb)

iso : Iso A B → Sampling A → Sampling B
iso iso sa db = mapR (iso .fwd) (sa (mapD (iso .bwd) db))

unit : Sampling ⊤
unit = λ _ → return _

maybe : Sampling A → Sampling (Maybe A)
maybe {A = A} sa = iso equiv (seq bool sT) where

  equiv : Iso (Σ Bool (if_then ⊤ else A)) (Maybe A)

  equiv .fwd (true  , _) = nothing
  equiv .fwd (false , a) = just a

  equiv .bwd nothing  = true , _
  equiv .bwd (just a) = false , a

  equiv .id₁ (true  , _) = refl
  equiv .id₁ (false , a) = refl

  equiv .id₂ nothing  = refl
  equiv .id₂ (just a) = refl

  sT : (b : Bool) → Sampling (if b then ⊤ else A)
  sT true  = unit
  sT false = sa

sum : Sampling A → Sampling B → Sampling (A ⊎ B)
sum {A = A} {B = B} sa sb = iso equiv (seq bool sT) where

  equiv : Iso (Σ Bool (if_then A else B)) (A ⊎ B)

  equiv .fwd (true  , a) = inj₁ a
  equiv .fwd (false , b) = inj₂ b

  equiv .bwd (inj₁ a) = true , a
  equiv .bwd (inj₂ b) = false , b

  equiv .id₁ (true  , a) = refl
  equiv .id₁ (false , b) = refl
  equiv .id₂ (inj₁ a) = refl
  equiv .id₂ (inj₂ b) = refl

  sT : (b : Bool) → Sampling (if b then A else B)
  sT true  = sa
  sT false = sb

{-# NON_TERMINATING #-}
list : Sampling A → Sampling (List A)
list {A = A} sa = iso equiv (maybe (prod sa (list sa))) where

  equiv : Iso (Maybe (A × List A)) (List A)
  equiv .fwd = maybe′ (uncurry _∷_) []
  equiv .bwd = uncons

  equiv .id₁ nothing  = refl
  equiv .id₁ (just _) = refl

  equiv .id₂ []       = refl
  equiv .id₂ (x ∷ xs) = refl
