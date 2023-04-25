{-# OPTIONS --guardedness #-}

module Data.Serialisable.Desc where

open import Agda.Builtin.FromNat using (fromNat)
open import Agda.Builtin.FromString using (IsString; fromString)

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Buffer using (Buffer; getWord8)
open import Data.Fin as Fin using (Fin)
open import Data.Nat.Base using (ℕ; suc; _+_)
import Data.Nat.Literals; instance NumberNat = Data.Nat.Literals.number
open import Data.Product.Base as Prod using (_×_; _,_)
open import Data.String as String using (String)
import Data.String.Literals; instance IsStringString = Data.String.Literals.isString
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.Any as Any using (Any; any?)
open import Data.Word8 as Word8 using (Word8)

open import Function.Base using (id; _∘_; const; case_of_)

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
open import Relation.Nullary.Decidable as Dec using (Dec; True; yes)

------------------------------------------------------------------------------
-- Core types

module Desc where

  data Desc (rightmost : Bool) : (static offsets : ℕ) → Set where
    none : Desc rightmost 0 0
    byte : Desc rightmost 1 0
    prod : {sl sr ol or : ℕ} →
           Desc false sl ol →
           Desc rightmost sr or →
           Desc rightmost (sl + sr) (ol + or)
    rec : Desc rightmost 0 (if rightmost then 0 else 1)

  _≡ᵇ_ : ∀ {r s o r′ s′ o′} → Desc r s o → Desc r′ s′ o′ → Bool
  none ≡ᵇ none = true
  byte ≡ᵇ byte = true
  prod d e ≡ᵇ prod d′ e′ = (d ≡ᵇ d′) ∧ (e ≡ᵇ e′)
  rec ≡ᵇ rec = true
  _ ≡ᵇ _ = false

open Desc hiding (module Desc) using (Desc; none; byte; prod; rec) public

module Constructor where

  record Constructor (nm : Set) : Set where
    constructor _∶_
    field
      name : nm
      {static} : ℕ
      {offsets} : ℕ
      description : Desc true static offsets
  open Constructor public

  _≡ᵇ_ : {nm nm′ : Set} → Constructor nm → Constructor nm′ → Bool
  (_ ∶ d) ≡ᵇ (_ ∶ d′) = d Desc.≡ᵇ d′

open Constructor hiding (module Constructor) using (Constructor; _∶_)

module Data where

  record Data (nm : Set) : Set where
    constructor mkData
    field
      {consNumber} : ℕ
      constructors : Vec (Constructor nm) consNumber
  open Data public

  _≡ᵇ_ : ∀ {n nm nm′} → Vec (Constructor nm) n → Vec (Constructor nm′) n → Bool
  cs ≡ᵇ cs′ = Vec.foldr (const Bool) _∧_ true (Vec.zipWith Constructor._≡ᵇ_ cs cs′)

open Data hiding (module Data) using (Data; mkData; consNumber; constructors)

record Index {nm : Set} (cs : Data nm) : Set where
  constructor mkIndex
  field getIndex : Fin (consNumber cs)
open Index public

------------------------------------------------------------------------------
-- Operations

-- A smart projection
description :
  {nm : Set} {cs : Data nm} (k : Index cs) →
  let cons = Vec.lookup (constructors cs) (getIndex k) in
  let open Constructor in
  Desc true (Constructor.static cons) (offsets cons)
description {cs = cs} k = Constructor.description (Vec.lookup (constructors cs) (getIndex k))

instance
  IsStringIndex : {cs : Data String} → IsString (Index cs)
  IsStringIndex {cs} .IsString.Constraint str
    = True (any? ((str String.≟_) ∘ Constructor.name) (constructors cs))
  IsStringIndex {cs} .IsString.fromString str
    with (any? ((str String.≟_) ∘ Constructor.name) (constructors cs))
  ... | yes p = mkIndex (Any.index p)

_≟_ : {nm : Set} {cs : Data nm} (p q : Index cs) → Dec (p ≡ q)
mkIndex k ≟ mkIndex l = Dec.map′ (cong mkIndex) (cong getIndex) (k Fin.≟ l)


------------------------------------------------------------------------
-- Reading descriptions from buffers

record IDesc (rightmost : Bool) : Set where
  constructor mkIDesc
  field
    {static} : ℕ
    {offsets} : ℕ
    runIDesc : Desc rightmost static offsets
open IDesc

iprod : ∀ {r} → IDesc false → IDesc r → IDesc r
iprod (mkIDesc d) (mkIDesc e) = mkIDesc (prod d e)


data Deserialising {a} (A : Set a) : Set a where
  failedToDeserialiseAt : ℕ → Deserialising A
  pure : (ℕ × A) → Deserialising A

_>>=_ : ∀ {a b} {A : Set a} {B : Set b} →
        Deserialising A → ((ℕ × A) → Deserialising B) →
        Deserialising B
failedToDeserialiseAt idx >>= k = failedToDeserialiseAt idx
pure x >>= k = k x

module _ (buf : Buffer) where

  -- TODO: use coinductive IO instead?
  {-# NON_TERMINATING #-}
  getDesc : ∀ {r} → (start : ℕ) → Deserialising (IDesc r)
  getDesc start = case Word8.toℕ (getWord8 buf start) of λ where
    0 → pure (1 + start , mkIDesc none)
    1 → pure (1 + start , mkIDesc byte)
    2 → do (middle , d) ← getDesc (1 + start)
           (end , e) ← getDesc middle
           pure (end , iprod d e)
    3 → pure (1 + start , mkIDesc rec)
    _ → failedToDeserialiseAt start

  getConstructors : (start n : ℕ) → Deserialising (Vec (Constructor ⊤) n)
  getConstructors start 0 = pure (start , [])
  getConstructors start (suc n)
    = do (middle , c) ← getDesc start
         (end , cs) ← getConstructors middle n
         pure (end , (_ ∶ runIDesc c) ∷ cs)

  getData : (start : ℕ) → Deserialising (Data ⊤)
  getData start
    = do let n = Word8.toℕ (getWord8 buf start)
         let middle = 1 + start
         (end , cs) ← getConstructors middle n
         pure (end , mkData cs)

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
  mkμ : Alg cs (μ cs)

{-# TERMINATING #-}
fold : ∀ {nm cs a} → Alg cs a → μ {nm} cs → a
fold φ (mkμ k t) = φ k (fmap _ (fold φ) t)

------------------------------------------------------------------------
-- Examples

module Tree where

  Leaf Node : Constructor String

  Leaf = "leaf" ∶ none
  Node = "node" ∶ prod rec (prod byte rec)

  Tree : Data String
  Tree = mkData (Leaf ∷ Node ∷ [])

  leaf : μ Tree
  leaf = mkμ "leaf" _

  node : μ Tree → Word8 → μ Tree → μ Tree
  node l b r = mkμ "node" (l , b , r)

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
