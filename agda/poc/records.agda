module records where

open import Size
open import Level
open import Data.Bool.Base
open import Data.List.Base
open import Data.Product
open import Data.String using (String; _≟_)
open import Data.Unit.Base
open import Relation.Nullary using (does)

variable
  i : Size

------------------------------------------------------------------------
-- ROSE TREES
------------------------------------------------------------------------

data Rose : Size → Set where
  node : String → List (Rose i) → Rose (↑ i)

data Zipper : Set where
  hole : Zipper
  node : String → List (Rose ∞) → Zipper → List (Rose ∞) → Zipper

freshᴿ  : String → Rose i → Bool
freshᴸ : String → List (Rose i) → Bool

freshᴿ str (node nm rs) = not (does (str ≟ nm))
                        ∧ freshᴸ str rs

freshᴸ str []       = true
freshᴸ str (r ∷ rs) = freshᴿ str r
                    ∧ freshᴸ str rs

fresh : String → Zipper → Bool
fresh str hole                 = true
fresh str (node nm bef zp aft) = not (does (str ≟ nm))
                               ∧ freshᴸ str bef
                               ∧ fresh str zp
                               -- do not look to the right

------------------------------------------------------------------------
-- RECORD TYPES
------------------------------------------------------------------------

-- A record type is defined by induction over a rose tree of names.
-- Each name stands for a field and gets an associated `Set`. This
-- `Set` may only depend on the ones coming from above in the rose
-- tree. In other words the structure of the tree helps us track the
-- dependencies.

-- This means that if we were to shuffle the list of subtrees, we
-- ought to end up with an isomorphic type.


Recordᴿ : Zipper → Rose i → Set → Set₁
Recordᴸ : String → List (Rose ∞) → Zipper → List (Rose i) → Set → Set₁

Recordᴿ zp (node str rs) A = T (fresh str zp)
                           × Σ[ B ∈ (A → Set) ]
                             Recordᴸ str [] zp rs (Σ A B)

Recordᴸ str bef zp []        A = Lift _ ⊤
Recordᴸ str bef zp (r ∷ aft) A = Recordᴿ (node str bef zp aft) r A
                               × Recordᴸ str (r ∷ bef) zp aft A

Record : List (Rose ∞) → Set₁
Record names = Recordᴸ "" [] hole names ⊤

------------------------------------------------------------------------
-- RECORD VALUES
------------------------------------------------------------------------

-- Once we have the record types, we can compute the corresponding notion
-- of record value. Basically: computed nested Σ-types making sure we store
-- a value of the appropriate type for each field.

Valueᴿ : (zp : Zipper) (names : Rose i) (A : Set)
       → Recordᴿ {i = i} zp names A → A → Set
Valueᴸ : (nm : String) (bef : List (Rose ∞)) (zp : Zipper)
       → (aft : List (Rose i)) (A : Set)
       → Recordᴸ {i = i} nm bef zp aft A → A → Set


Valueᴿ zp (node str rs) A (_ , B , rec) a =
  Σ[ b ∈ B a ] Valueᴸ str [] zp rs (Σ A B) rec (a , b)

Valueᴸ nm bef zp []        A recs a = ⊤
Valueᴸ nm bef zp (r ∷ aft) A (rec , recs) a
  = Valueᴿ (node nm bef zp aft) r A rec a
  × Valueᴸ nm (r ∷ bef) zp aft A recs a

Value : ∀ names → Record names → Set
Value names r = Valueᴸ "" [] hole names ⊤ r _


------------------------------------------------------------------------
-- EXAMPLE
------------------------------------------------------------------------

-- I want:
-- record MyRecord : Set where
--   field
--     length : ℕ
--     vec₁   : Vec ℕ length
--     vec₂   : Vec ℕ length
--     val₁   : ℕ
--     val₂   : ℕ
--     prf    : val₁ ≡ val₂

MyFields : List (Rose _)
MyFields = node "length" (node "vec₁" [] ∷ node "vec₂" [] ∷ [])
         ∷ node "val₁" (node "val₂" (node "prf" [] ∷ []) ∷ [])
         ∷ []

open import Function.Base
open import Data.Nat.Base
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality

MyRecord : Record MyFields
MyRecord = (_ , (λ _ → ℕ) , (_ , Vec ℕ ∘ proj₂ , _)
                          , (_ , Vec ℕ ∘ proj₂ , _)
                          , _)
         , (_ , (λ _ → ℕ) , (_ , (λ _ → ℕ) , (_ , (λ ((_ , m) , n) → m ≡ n) , _)
                                           , _)
                          , _)
         , _


MyValue : Value MyFields MyRecord
MyValue = (3 , (1 ∷ 2 ∷ 3 ∷ [] , _) , (5 ∷ 6 ∷ 7 ∷ [] , _) , _)
        , (4 , (2 + 2 , (refl , _) , _) , _)
        , _
