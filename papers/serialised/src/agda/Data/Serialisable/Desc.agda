{-# OPTIONS --erasure #-}

module Data.Serialisable.Desc where

open import Agda.Builtin.FromNat using (fromNat)
open import Agda.Builtin.FromString using (IsString; fromString)

open import Data.Bool.Base using (Bool; true; false; T; if_then_else_; _∧_)
open import Data.Buffer using (Buffer; getWord8)
open import Data.Buffer.Builder using (Builder; word8; empty; _<>_)
open import Data.Fin as Fin using (Fin)
open import Data.Int64 as Int64 using (Int64; _+_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; suc; _≤ᵇ_)
import Data.Nat.Literals; instance NumberNat = Data.Nat.Literals.number
open import Data.Product.Base as Prod using (_×_; _,_)
open import Data.String as String using (String; parens; _++_)
import Data.String.Literals; instance IsStringString = Data.String.Literals.isString
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.Any as Any using (Any; any?)
open import Data.Word8 as Word8 using (Word8; word8AsBoundedNat)

open import Function.Base using (id; _∘_; _∘′_; _$_; const; case_of_)

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
           Desc rightmost (sl ℕ.+ sr) (ol ℕ.+ or)
    rec : Desc rightmost 0 (if rightmost then 0 else 1)

  _≡ᵇ_ : ∀ {r s o r′ s′ o′} → Desc r s o → Desc r′ s′ o′ → Bool
  none ≡ᵇ none = true
  byte ≡ᵇ byte = true
  prod d e ≡ᵇ prod d′ e′ = (d ≡ᵇ d′) ∧ (e ≡ᵇ e′)
  rec ≡ᵇ rec = true
  _ ≡ᵇ _ = false

  showPrec : ∀ {r s o} → ℕ → Desc r s o → String
  showPrec lvl none = "()"
  showPrec lvl byte = "Word8"
  showPrec lvl (prod d e)
    = (if 1 ≤ᵇ lvl then parens else id) (showPrec 0 d ++ " * " ++ showPrec 1 e)
  showPrec lvl rec = "X"

  show : ∀ {r s o} → Desc r s o → String
  show = showPrec 0

open Desc hiding (module Desc) using (Desc; none; byte; prod; rec) public

module Constructor where

  record Constructor (@0 nm : Set) : Set where
    constructor _∶_
    field
      name : nm
      {static} : ℕ
      {offsets} : ℕ
      description : Desc true static offsets
  open Constructor public

  _≡ᵇ_ : {@0 nm nm′ : Set} → Constructor nm → Constructor nm′ → Bool
  (_ ∶ d) ≡ᵇ (_ ∶ d′) = d Desc.≡ᵇ d′

open Constructor public hiding (module Constructor) using (Constructor; _∶_)

module Data where

  record Data (@0 nm : Set) : Set where
    constructor mkData
    field
      {consNumber} : ℕ
      @0 {{fitsInBits8}} : T (consNumber ≤ᵇ 255)
      constructors : Vec (Constructor nm) consNumber
  open Data public

  _≡ᵇ_ : ∀ {@0 nm nm′} → Data nm → Data nm′ → Bool
  d ≡ᵇ d′ = go (constructors d) (constructors d′) where

    go : ∀ {@0 nm nm′ n n′} → Vec (Constructor nm) n → Vec (Constructor nm′) n′ → Bool
    go [] [] = true
    go (c ∷ cs) (c′ ∷ cs′) = c Constructor.≡ᵇ c′ ∧ go cs cs′
    go _ _ = false


  show : ∀ {@0 nm} → Data nm → String
  show {nm} cs = go (constructors cs) where

    go : ∀ {n} → Vec (Constructor nm) n → String
    go [] = "⊥"
    go (c ∷ cs) = String.concat
      $ ("μX. " ++ Desc.show (Constructor.description c))
      ∷ List.map ((" + " ++_) ∘′ Desc.show ∘ Constructor.description) (Vec.toList cs)

open Data public hiding (module Data) using (Data; mkData; consNumber; constructors)

record Index {@0 nm : Set} (@0 cs : Data nm) : Set where
  constructor mkIndex
  field getIndex : Fin (consNumber cs)
open Index public

------------------------------------------------------------------------------
-- Operations

-- A smart projection
description :
  {@0 nm : Set} {cs : Data nm} (k : Index cs) →
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

_≟_ : {@0 nm : Set} {cs : Data nm} (p q : Index cs) → Dec (p ≡ q)
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
  failedToDeserialiseAt : Int64 → Deserialising A
  pure : (Int64 × A) → Deserialising A

_>>=_ : ∀ {a b} {A : Set a} {B : Set b} →
        Deserialising A → ((Int64 × A) → Deserialising B) →
        Deserialising B
failedToDeserialiseAt idx >>= k = failedToDeserialiseAt idx
pure x >>= k = k x

module _ (buf : Buffer) where

  -- TODO: use coinductive IO instead?
  {-# NON_TERMINATING #-}
  getDesc : ∀ {r} → (start : Int64) → Deserialising (IDesc r)
  getDesc start = case Word8.toℕ (getWord8 buf start) of λ where
    0 → pure (1 + start , mkIDesc none)
    1 → pure (1 + start , mkIDesc byte)
    2 → do (middle , d) ← getDesc (1 + start)
           (end , e) ← getDesc middle
           pure (end , iprod d e)
    3 → pure (1 + start , mkIDesc rec)
    _ → failedToDeserialiseAt start

  getConstructors : (start : Int64) (n : ℕ) → Deserialising (Vec (Constructor ⊤) n)
  getConstructors start 0 = pure (start , [])
  getConstructors start (suc n)
    = do (middle , c) ← getDesc start
         (end , cs) ← getConstructors middle n
         pure (end , (_ ∶ runIDesc c) ∷ cs)

  getData : (start : Int64) → Deserialising (Data ⊤)
  getData start
    = do let i = getWord8 buf start
         let (n , oh) = word8AsBoundedNat i
         let middle = 1 + start
         (end , cs) ← getConstructors middle n
         pure (end , mkData {{oh}} cs)

------------------------------------------------------------------------
-- Serialisation of descriptions to a Buffer

setDesc : ∀ (start : ℕ) {@0 r s o} → Desc r s o → ℕ × Builder
setDesc start none = (suc start , word8 0)
setDesc start byte = (suc start , word8 1)
setDesc start (prod d e)
  = let (middle , builder₂) = setDesc start d in
    let (end , builder₃) = setDesc middle e in
    (end , word8 2 <> builder₂ <> builder₃)
setDesc start rec = (suc start , word8 3)

setConstructors : ∀ (start : ℕ) {@0 nm n} → Vec (Constructor nm) n → ℕ × Builder
setConstructors start [] = start , empty
setConstructors start (c ∷ cs)
  = let (middle , builder₁) = setDesc start (Constructor.description c) in
    let (end , builder₂) = setConstructors middle cs in
    end , builder₁ <> builder₂

setData :  ∀ (start : ℕ) {@0 nm} → Data nm → ℕ × Builder
setData start cs
  = let (end , builder₂) = setConstructors (suc start) (constructors cs) in
    end , word8 (Word8.fromℕ (consNumber cs)) <> builder₂
