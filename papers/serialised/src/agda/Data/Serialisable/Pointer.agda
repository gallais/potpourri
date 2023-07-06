{-# OPTIONS --guardedness --erasure #-}

module Data.Serialisable.Pointer where

open import Level using (_⊔_; lower)

open import Agda.Builtin.FromNat using (fromNat)

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Buffer as Buffer using (Buffer; getWord8; getWord64; getInt64; slice)
open import Data.Buffer.Builder
open import Data.Default
import Data.Fin.Base as Fin
open import Data.Int64 as Int64 using (Int64; _≡ᵇ_)
open import Data.List.Base using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<?_)
open import Data.Product as Prod using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Singleton using (Singleton; mkSingleton)
open import Data.String.Base using (String; unlines)
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base as Vec using (Vec; _∷_; []; _++_)
open import Data.Word8 as Word8 using (Word8)
open import Data.Word as Word64 using (Word64)

open import Function.Base using (_$_)

open import IO using (IO) hiding (module IO)
open import Data.Buffer.IO as Buffer
open import System.Exit

open import Data.Singleton using (Singleton; unsafeMkSingleton; getSingleton)
open import Data.Serialisable.Desc hiding (pure; _>>=_)
open import Data.Serialisable.Data as Data hiding (module Tree)

open import Function.Base using (case_of_; _∘_; _$′_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym)
open import Relation.Nullary using (yes; no)

private
  variable
    r : Bool
    s o : ℕ
    nm : Set

postulate error : ∀ {a} {A : Set a} → String → A
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC error = \ _ _ -> error . T.unpack #-}

record ∃ {a p} {A : Set a} (P : A → Set p) : Set (a ⊔ p) where
  constructor _,_
  field
    @0 proj₁ : A
    proj₂ : P proj₁

abstract

  infix 3 ⟦_⟧μ_∋_
  record ⟦_⟧μ_∋_ (d : Desc r s o) (cs : Data nm) (t : ⟦ d ⟧ (μ cs)) : Set where
    constructor mkMeaning
    field
      meaningOffsets : Vec Word64 o
      meaningBuffer : Buffer
      meaningPosition : Int64
      meaningSize : ℕ

  infix 3 μ_∋_
  record μ_∋_ (cs : Data nm) (t : μ cs) : Set where
    constructor mkMu
    field
      muBuffer : Buffer
      muPosition : Int64
      muSize : ℕ

Poke : (d : Desc r s o) (cs : Data nm) (t : ⟦ d ⟧ (μ cs)) → Set
Poke none cs t = ⊤
Poke byte cs t = Singleton t
Poke (prod d e) cs (s , t) = ⟦ d ⟧μ cs ∋ s × ⟦ e ⟧μ cs ∋ t
Poke rec cs t = μ cs ∋ t


abstract

  poke : {d : Desc r s o} {@0 cs : Data nm} {@0 t : ⟦ d ⟧ (μ cs)} →
         ⟦ d ⟧μ cs ∋ t → Poke d cs t
  poke {d = none} ptr = _
  poke {d = byte} (mkMeaning off buf pos size)
    = unsafeMkSingleton (getWord8 buf pos)
  poke {d = prod {sl = sl} {ol = ol} d e} (mkMeaning off buf pos size)
    = let (offl , offr , _) = Vec.splitAt ol off in
      let sizel = Vec.sum (Vec.map Word64.toℕ offl) + sl in
      let left = mkMeaning offl buf pos sizel in
      let right = mkMeaning offr buf (pos Int64.+ Int64.fromℕ sizel) (size ∸ sizel) in
      (left , right)
  poke {d = rec} (mkMeaning off buf pos size) = mkMu buf pos size


Layer : (d : Desc r s o) (cs : Data nm) (t : ⟦ d ⟧ (μ cs)) → Set
Layer none cs t = ⊤
Layer byte cs t = Singleton t
Layer (prod d e) cs (s , t) = Layer d cs s × Layer e cs t
Layer rec cs t = μ cs ∋ t

abstract

  layer : {d : Desc r s o} {@0 cs : Data nm} {@0 t : ⟦ d ⟧ (μ cs)} →
          ⟦ d ⟧μ cs ∋ t → Layer d cs t
  layer {d = d} ptr = go d (poke ptr) where

    go :  (d : Desc r s o) {@0 cs : Data nm} {@0 t : ⟦ d ⟧ (μ cs)} →
          Poke d cs t → Layer d cs t
    go none p = p
    go byte p = p
    go (prod d e) (p , q) = layer p , layer q
    go rec p = p

data Out (cs : Data nm) : (@0 t : μ cs) → Set where
  _,_ : (k : Index cs) →
        ∀ {@ 0 t} → ⟦ description k ⟧μ cs ∋ t →
        Out cs (k , t)

getOffsets :
  Buffer → Int64 → -- Buffer & position
  (n : ℕ) → (Vec Word64 n × Int64)
getOffsets buf pos zero = ([] , pos)
getOffsets buf pos (suc n)
  = Prod.map₁ (getWord64 buf pos ∷_) (getOffsets buf (pos Int64.+ 8) n)

abstract

  getConstructor :
    {cs : Data nm} (k : Index cs) →
    ∀ {@0 t} → μ cs ∋ k , t → ⟦ description k ⟧μ cs ∋ t
  getConstructor {cs = cs} tag {t} (mkMu buf pos size)
    = let offs = Constructor.offsets (Vec.lookup (constructors cs) (getIndex tag)) in
      let (offsets , pos) = getOffsets buf (1 Int64.+ pos) offs in
      let size = size ∸ 1 ∸ (8 * offs) in
      mkMeaning offsets buf pos size

  out : ∀ {cs : Data nm} {@0 t} → μ cs ∋ t → Out cs t
  out {cs = cs} {t} ptr@(mkMu buf pos size)
    = let tag = Word8.toℕ (getWord8 buf pos) in
      case tag <? consNumber cs of λ where
        (no _) → error "Invalid representation"
        (yes tag<n) →
          let k = mkIndex (Fin.fromℕ< tag<n) in
          let @0 sub : _; sub = unfoldAs k t in
          coerce (Out cs) (sym (proj₂ sub))
            (k , getConstructor k (coerce (μ cs ∋_) (proj₂ sub) ptr))

    where

      coerce : ∀ (@0 P : @0 μ cs → Set) {@0 s t} (@0 eq : s ≡ t) → P s → P t
      coerce P refl v = v

      postulate
        @0 unfoldAs :
          (k : Index cs) (t : μ cs) →
          Σ[ v ∈ ⟦ description k ⟧ (μ cs) ] t ≡ (k , v)


data View (cs : Data nm) : (@0 t : μ cs) → Set where
  _,_ : (k : Index cs) →
        ∀ {@ 0 t} → Layer (description k) cs t →
        View cs (k , t)

abstract

  view : ∀ {cs : Data nm} {@0 t} → μ cs ∋ t → View cs t
  view ptr with out ptr
  ... | k , t = k , layer t

  initFromFile : {{safe : WithDefault true}} {nm : Set} (cs : Data nm) → String → IO (∃ (μ cs ∋_))
  initFromFile {{safe}} cs fp
    = let open IO; open Deserialising in do
         buf ← readFile fp
         let skip = getWord64 buf 0
         when (value safe) $′ do
           pure (_ , cs′) ← pure (getData buf 8)
             where _ → die "oops"
           unless (cs Data.≡ᵇ cs′) $′ die $′ unlines
             $′ "Description mismatch:"
             ∷ "expected:"
             ∷ Data.show cs
             ∷ "but got:"
             ∷ Data.show cs′
             ∷ []
         let pos = Int64.fromℕ (Word64.toℕ skip) Int64.+ 8
         pure (t , mkMu buf pos (Buffer.length buf ∸ Int64.toℕ pos))

    where postulate @0 t : μ cs -- postulated as an abstract value

deserialise : {cs : Data nm} → ∀ {@0 t} → μ cs ∋ t → Singleton t
deserialise {cs = cs} ptr with view ptr
... | k , v = (k ,_) <$> go _ v where

  open Data.Singleton

  go : (d : Desc r s o) → ∀ {@0 t} → Layer d cs t → Singleton t
  go none v = ⦇ _ ⦈
  go byte v = v
  go (prod d e) (l , r) = ⦇ go d l , go e r ⦈
  go rec v = deserialise v


abstract

  record Serialising {@0 nm} (@0 cs : Data nm) (@0 t : μ cs) : Set₁ where
    constructor mkSerialising
    field runSerialising : ℕ × Builder
  open Serialising

  goMeaning :
    ∀ {r} {@0 s o nm} (d : Desc r s o) {@0 cs : Data nm} →
    {@0 t : ⟦ d ⟧ (μ cs)} →
    All d (λ t → Serialising cs t) (λ w → Singleton w) t →
    (ℕ × Builder × Vec ℕ o)
  goMeaning none vs = (0 , empty , [])
  goMeaning byte vs = (1 , word8 (getSingleton $ lower vs) , [])
  goMeaning (prod d e) (vs , ws)
    = let (size₁ , builder₁ , offs₁) = goMeaning d vs in
      let (size₂ , builder₂ , offs₂) = goMeaning e ws in
      size₁ + size₂ , builder₁ <> builder₂ , offs₁ ++ offs₂
  goMeaning {r} rec vs with (size , builder) ← runSerialising (lower vs) | r
  ... | true = size , builder , []
  ... | false = size , builder , size ∷ []

  goMu : ∀ {@0 nm} {cs : Data nm} →
         (idx : Index cs) (c : Constructor nm) →
         {@0 t : ⟦ Constructor.description c ⟧ (μ cs)} →
         All (Constructor.description c) (λ t → Serialising cs t) (λ w → Singleton w) t →
         ℕ × Builder
  goMu idx c vs
    = let size₁      = 1 in
      let builder₁   = word8 (Word8.fromℕ (Fin.toℕ (getIndex idx))) in
      let size₂      = 8 * Constructor.offsets c in
      let (size₃ , builder₃ , is) = goMeaning (Constructor.description c) vs in
      let builder₂   = Vec.foldr′ (λ i → int64LE (Int64.fromℕ i) <>_) empty is in
      size₁ + size₂ + size₃ , builder₁ <> builder₂ <> builder₃

  _#_ : ∀ {@0 nm} {cs : Data nm} (k : Index cs) →
        {@0 t : ⟦ description k ⟧ (μ cs)} ->
        All (description k) (λ t → Serialising cs t) (λ w → Singleton w) t →
        Serialising cs (k , t)
  _#_ {cs = cs} k layer
    = mkSerialising $ goMu k (Vec.lookup (constructors cs) (getIndex k)) layer

  {-# TERMINATING #-}
  serialise : ∀ {@0 nm} {cs : Data nm} (t : μ cs) → Serialising cs t
  serialise (k , t) = k # all (description k) serialise mkSingleton t

  execSerialising : ∀ {@0 nm} {cs : Data nm} {@0 t : μ cs} →
                    Serialising cs t → μ cs ∋ t
  execSerialising {cs = cs} ser
    = let (size₁ , builder₁) = setData 8 cs in
      let (size₂ , builder₂) = runSerialising ser in
      let builder = int64LE (Int64.fromℕ size₁) <> builder₁ <> builder₂ in
      mkMu (toBuffer builder) (8 Int64.+ Int64.fromℕ size₁) size₂

  writeToFile : ∀ {@0 nm} {cs : Data nm} → String →
                ∀ {@0 t} → μ cs ∋ t → IO ⊤
  writeToFile fp (mkMu buf pos size) = let open IO in do
    let desc = getInt64 buf 0
    let start = 8 Int64.+ desc
    let buf = if pos ≡ᵇ start then buf
              else toBuffer (buffer (slice 0 start buf)
                          <> buffer (slice pos (Int64.fromℕ size) buf))
    Buffer.writeFile fp buf

module Tree where

  open Data.Tree using (Tree)
  open Data.Tree.P
  open Data.Singleton

  sum : ∀ {@0 t} → μ Tree ∋ t → Singleton (Data.Tree.sum t)
  sum t with view t
  ... | leaf , _ = ⦇ 0 ⦈
  ... | node , l , b , r
    = let m = sum l
          n = sum r
      in ⦇ ⦇ m + ⦇ Word8.toℕ b ⦈ ⦈ + n ⦈

  open import Data.Maybe.Base using (Maybe; nothing; just; _<∣>_)

  right : ∀ {@0 t} → μ Tree ∋ t → Singleton (Data.Tree.right t)
  right t with view t
  ... | leaf , _ = ⦇ nothing ⦈
  ... | node , l , b , r = ⦇ right r <∣> ⦇ just b ⦈ ⦈

  leftBranch : ∀ {@0 t} → μ Tree ∋ t → μ Tree ∋ Data.Tree.leftBranch t
  leftBranch t with view t
  ... | leaf , _ = t
  ... | node , l , _ , _ = l
