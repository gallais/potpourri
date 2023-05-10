module Data.Serialisable.Data where

open import Agda.Builtin.FromNat using (fromNat)
open import Agda.Builtin.FromString using (fromString)

open import Data.Product as Prod using (_×_; _,_)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base using (_∷_; [])
open import Data.Word8 as Word8 using (Word8)

open import Function.Base using (id)

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

data μ {nm} (cs : Data nm) : Set where
  _,_ : Alg cs (μ cs)

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
