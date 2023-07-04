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
-- Meaning as trees

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

Alg : ∀ {nm} → Data nm → Set → Set
Alg cs X = (k : Index cs) → ⟦ description k ⟧ X → X

data μ {@0 nm} (@0 cs : Data nm) : Set where
  _,_ : Alg cs (μ cs)

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

{-# TERMINATING #-}
fold : ∀ {nm cs a} → Alg cs a → μ {nm} cs → a
fold φ (k , t) = φ k (fmap _ (fold φ) t)

------------------------------------------------------------------------
-- Examples

module Tree where

  Leaf Node : Constructor String

  Leaf = "leaf" ∶ none
  Node = "node" ∶ prod rec (prod byte rec)

  Tree : Data String
  Tree = mkData (Leaf ∷ Node ∷ [])

  module P where
    open import Data.Fin.Base using (zero; suc)
    pattern leaf = mkIndex zero
    pattern node = mkIndex (suc zero)

  showi : String → μ Tree → String
  showi pad t = unlines (let (hd ∷ tl) = go 0 pad t [] in (pad String.++ hd) ∷ tl) where

    open P

    go : ℕ → String → μ Tree → List String → List⁺ String
    go closings pad (leaf , _) = ("leaf" String.++ String.replicate closings ')') ∷_
    go closings pad (node , (leaf , _) , b , (leaf , _))
      = let byte = ℕ.show (Word8.toℕ b) in
        (unwords ("(node" ∷ "leaf" ∷ byte ∷ "leaf" ∷ []) String.++ String.replicate (suc closings) ')') ∷_
    go closings pad (node , l , b , r) acc
      = let pad = "      " String.++ pad in
        let hd₁ ∷ tl₁ = go (suc closings) pad r acc in
        let byte = pad String.++ ℕ.show (Word8.toℕ b) in
        let hd₂ ∷ tl₂ = go 0 pad l $′ byte ∷ (pad String.++ hd₁) ∷ tl₁ in
        ("(node " String.++ hd₂) ∷ tl₂

  show : μ Tree → String
  show = showi ""

  leaf : μ Tree
  leaf = "leaf" , _

  node : μ Tree → Word8 → μ Tree → μ Tree
  node l b r = "node" , l , b , r

  example : μ Tree
  example =
    (node
      (node (node leaf 1 leaf) 5 leaf)
      10
      (node leaf 20 leaf))

  bigexample : μ Tree
  bigexample =
    (node
      (node (node leaf 1 leaf) 5 leaf)
      10
      (node leaf 20
        (node
          (node leaf 56 (node leaf 5 leaf))
          17
          (node leaf 23
            (node leaf 78 leaf)))))

  open P

  sum : μ Tree → ℕ
  sum (leaf , _) = 0
  sum (node , l , b , r)
    = let m = sum l
          n = sum r
      in m + Word8.toℕ b + n

  right : μ Tree → Maybe Word8
  right (leaf , _) = nothing
  right (node , l , b , r)
    = right r <∣> just b
