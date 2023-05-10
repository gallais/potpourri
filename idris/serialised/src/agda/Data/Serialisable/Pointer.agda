{-# OPTIONS --guardedness --erasure #-}

module Data.Serialisable.Pointer where

open import Level using (_⊔_)

open import Data.Bool.Base using (Bool; true)
open import Data.Buffer as Buffer using (Buffer; getWord8; getWord64)
import Data.Fin.Base as Fin
open import Data.Default
open import Data.List.Base using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<?_)
open import Data.Product as Prod using (Σ-syntax; _×_; _,_; proj₂)
open import Data.String.Base using (String; unlines)
open import Data.Unit.Base using (⊤)
open import Data.Vec.Base as Vec using (Vec; _∷_; [])
open import Data.Word8 as Word8 using (Word8)
open import Data.Word as Word64 using (Word64)

open import IO
open import Data.Buffer.IO
open import System.Exit

open import Data.Singleton using (Singleton; unsafeMkSingleton; getSingleton)
open import Data.Serialisable.Desc hiding (_>>=_)
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
      meaningPosition : ℕ
      meaningSize : ℕ

  infix 3 μ_∋_
  record μ_∋_ (cs : Data nm) (t : μ cs) : Set where
    constructor mkMu
    field
      muBuffer : Buffer
      muPosition : ℕ
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
      let right = mkMeaning offr buf (pos + sizel) (size ∸ sizel) in
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
  Buffer → ℕ → -- Buffer & position
  (n : ℕ) → (Vec Word64 n × ℕ)
getOffsets buf pos zero = ([] , pos)
getOffsets buf pos (suc n)
  = Prod.map₁ (getWord64 buf pos ∷_) (getOffsets buf (pos + 8) n)

abstract

  getConstructor :
    {cs : Data nm} (k : Index cs) →
    ∀ {@0 t} → μ cs ∋ k , t → ⟦ description k ⟧μ cs ∋ t
  getConstructor {cs = cs} tag {t} (mkMu buf pos size)
    = let offs = Constructor.offsets (Vec.lookup (constructors cs) (getIndex tag)) in
      let (offsets , pos) = getOffsets buf (1 + pos) offs in
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
    = do buf ← readFile fp
         let skip = getWord64 buf 0
         when (value safe) $′ do
           pure (_ , cs′) ← pure (getData buf 8)
             where _ → die "oops"
           unless (cs Data.≡ᵇ cs′) $′ die $′ unlines
             $′ "Description mismatch:"
             ∷ "expected:"
  --           ∷ show cs
             ∷ "but got:"
    --         ∷ show cs'
             ∷ []
         let pos = Word64.toℕ skip + 8
         pure (t , mkMu buf pos (Buffer.length buf ∸ pos))

    where postulate @0 t : μ cs -- postulated as an abstract value

module Tree where

  open Data.Tree
  open Data.Tree.P

  sum : ∀ {@0 t} → μ Tree ∋ t → ℕ
  sum t with view t
  ... | leaf , _ = 0
  ... | node , l , b , r
    = let m = sum l
          n = sum r
      in m + Word8.toℕ (getSingleton b) + n

  open import Data.Maybe.Base using (Maybe; nothing; just; _<∣>_)

  right : ∀ {@0 t} → μ Tree ∋ t → Maybe Word8
  right t with view t
  ... | leaf , _ = nothing
  ... | node , l , b , r = right r <∣> just (getSingleton b)
