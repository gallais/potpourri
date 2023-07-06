{-# OPTIONS --erasure #-}

module Data.Serialisable.Data where

open import Agda.Builtin.FromNat using (fromNat)
open import Agda.Builtin.FromString using (fromString)

open import Data.List.Base using (List; _∷_; []; _++_)
open import Data.List.NonEmpty using (List⁺; _∷_; toList)
open import Data.Maybe.Base using (Maybe; nothing; just; _<∣>_)
open import Data.Nat.Base using (ℕ; suc; _+_)
import Data.Nat.Show as ℕ
open import Data.Product as Prod using (_×_; _,_)
open import Data.String.Base as String using (String; unlines; unwords)
open import Data.String.Literals; instance StringIsString = isString
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base using (_∷_; [])
open import Data.Word8 as Word8 using (Word8)

open import Function.Base using (id; _$′_)

open import Level using (Lift; lift; _⊔_)

open import Data.Singleton
open import Data.Serialisable.Desc

------------------------------------------------------------------------
-- Meaning as functors

⟦_⟧ : ∀ {r s o} → Desc r s o → Set → Set
⟦ none ⟧ X = ⊤
⟦ byte ⟧ X = Word8
⟦ prod d e ⟧ X = ⟦ d ⟧ X × ⟦ e ⟧ X
⟦ rec ⟧ X = X

fmap : ∀ {r s o} (d : Desc r s o) {X Y} → (X → Y) → ⟦ d ⟧ X → ⟦ d ⟧ Y
fmap none f = id
fmap byte f = id
fmap (prod d e) f = Prod.map (fmap d f) (fmap e f)
fmap rec f = f

@0 All : ∀ {p q r s o X} (d : Desc r s o)
         (P : X → Set p) (Q : Word8 → Set q) →
         (t : ⟦ d ⟧ X) → Set (p ⊔ q)
All none P Q v = Lift _ ⊤
All {p = p} byte P Q v = Lift p (Q v)
All (prod d e) P Q (v , w) = All d P Q v × All e P Q w
All {q = q} rec P Q v = Lift q (P v)

all : ∀ {p q r s o X} (d : Desc r s o)
      {P : X → Set p} {Q : Word8 → Set q} →
      (∀ x → P x) → (∀ w → Q w) →
      (t : ⟦ d ⟧ X) → All d P Q t
all none p q t = _
all byte p q w = lift (q w)
all (prod d e) p q (t , u) = all d p q t , all e p q u
all rec p q t = lift (p t)

------------------------------------------------------------------------
-- Meaning as fixpoints

Alg : ∀ {nm} → Data nm → Set → Set
Alg cs X = (k : Index cs) → ⟦ description k ⟧ X → X

data μ {@0 nm} (@0 cs : Data nm) : Set where
  _,_ : Alg cs (μ cs)

{-# TERMINATING #-}
fold : ∀ {nm cs a} → Alg cs a → μ {nm} cs → a
fold φ (k , t) = φ k (fmap _ (fold φ) t)
