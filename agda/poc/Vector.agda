module Vector where

open import Level
open import Data.Bool
open import Data.Nat using (ℕ)
open import Data.String
open import Data.List
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Nullary

infix 3 _∈_
data _∈_ {ℓᵃ : Level} {A : Set ℓᵃ} (a : A) : (args : List A) → Set ℓᵃ where
  z : {as : List A} → a ∈ a ∷ as
  s : {b : A} {as : List A} (pr : a ∈ as) → a ∈ b ∷ as

[Fields] : (ℓ : Level) {ℓᵃ : Level} {A : Set ℓᵃ} (args : List A) → Set (suc ℓ)
[Fields] ℓ []           = Lift ⊤
[Fields] ℓ (arg ∷ args) = Set ℓ × [Fields] ℓ args

record Fields (ℓ : Level) {ℓᵃ : Level} {A : Set ℓᵃ} (args : List A) : Set (suc ℓ) where
  constructor mkFields
  field
    fields : [Fields] ℓ args
open Fields public

[tabulate] : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} (args : List A) (ρ : {arg : A} (pr : arg ∈ args) → Set ℓ) → [Fields] ℓ args
[tabulate] []           ρ = lift tt
[tabulate] (arg ∷ args) ρ = ρ z , [tabulate] args (ρ ∘ s)

tabulate : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} {args : List A} (ρ : {arg : A} (pr : arg ∈ args) → Set ℓ) → Fields ℓ args
tabulate {args = args} = mkFields ∘ [tabulate] args

-- we start by defining an heterogeneous vector
[Vector] : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} (args : List A) (fs : [Fields] ℓ args) → Set (suc ℓ)
[Vector] []           f        = Lift ⊤
[Vector] (arg ∷ args) (f , fs) = f × [Vector] args fs

-- having a record wrapping the computation helps the type
-- inference engine.
record Vector {ℓ ℓᵃ : Level} {A : Set ℓᵃ} (args : List A) (fs : Fields ℓ args) : Set (suc ℓ) where
  constructor mkVector
  field
    vector : [Vector] args $ fields fs
open Vector public

-- It is possible to change the type of an element in a specific
-- position.
update[Fields] : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} {args : List A} {a : A} (pr : a ∈ args) →
                 Set ℓ → [Fields] ℓ args → [Fields] ℓ args
update[Fields] z      A (_ , fs) = A , fs
update[Fields] (s pr) A (f , fs) = f , update[Fields] pr A fs

updateFields : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} {args : List A} {a : A} (pr : a ∈ args) →
               Set ℓ → Fields ℓ args → Fields ℓ args
updateFields pr A fs = mkFields $ update[Fields] pr A $ fields fs

-- from this we can define an update operation filling a position
-- k with a new element no matter what its type is
infixr 5 [_∷=_⟨]_ _∷=_⟨_
[_∷=_⟨]_ : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} {args : List A} {fs : [Fields] ℓ args}
           {a : A} (pr : a ∈ args) {A : Set ℓ} (v : A)
           (v : [Vector] args fs) → [Vector] args (update[Fields] pr A fs)
[ z   ∷= a ⟨] (_ , v) = a , v
[ s k ∷= a ⟨] (w , v) = w , [ k ∷= a ⟨] v

_∷=_⟨_ : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} {args : List A} {fs : Fields ℓ args}
         {a : A} (pr : a ∈ args) {A : Set ℓ} (v : A)
         (v : Vector args fs) → Vector args (updateFields pr A fs)
b ∷= a ⟨ mkVector p = mkVector $ [ b ∷= a ⟨] p

-- we can always generate a dummy vector full of proofs of unit
[⟨Fields⟩] : (ℓ : Level) {ℓᵃ : Level} {A : Set ℓᵃ} (args : List A) → [Fields] ℓ args
[⟨Fields⟩] ℓ []           = lift tt
[⟨Fields⟩] ℓ (arg ∷ args) = Lift ⊤ , [⟨Fields⟩] ℓ args

⟨Fields⟩ : (ℓ : Level) {ℓᵃ : Level} {A : Set ℓᵃ} (args : List A) → Fields ℓ args
⟨Fields⟩ ℓ args = mkFields $ [⟨Fields⟩] ℓ args

[⟨⟩] : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} (args : List A) → [Vector] args ([⟨Fields⟩] ℓ args)
[⟨⟩] []           = lift tt
[⟨⟩] (arg ∷ args) = lift tt , [⟨⟩] args

⟨⟩ : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} {args : List A} → Vector args (⟨Fields⟩ ℓ args)
⟨⟩ = mkVector $ [⟨⟩] _


-- from this we can build a vector by successively updating
-- a dummy one until we're happy with the result.

[cast] : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} (args : List A)
         (v : [Vector] args $ [tabulate] args (const (Set ℓ))) → [Fields] ℓ args
[cast] []           v       = lift tt
[cast] (arg ∷ args) (w , v) = w , [cast] args v

cast : {ℓ ℓᵃ : Level} {A : Set ℓᵃ} {args : List A} (v : Vector args (tabulate (const (Set ℓ)))) → Fields ℓ args
cast = mkFields ∘ [cast] _ ∘ vector

nums : List String
nums = "Zero" ∷ "One" ∷ "Two" ∷ "Three" ∷ "Four" ∷ []

Type[0⋯4] : Vector nums $ tabulate $ const Set
Type[0⋯4] = z               ∷= ℕ ⟨
            s z             ∷= ℕ ⟨
            s (s z)         ∷= ℕ ⟨
            s (s (s z))     ∷= ℕ ⟨
            s (s (s (s z))) ∷= ℕ ⟨
            ⟨⟩

0⋯4 : Vector nums $ cast Type[0⋯4]
0⋯4 = z               ∷= 0 ⟨
      s z             ∷= 1 ⟨
      s (s z)         ∷= 2 ⟨
      s (s (s z))     ∷= 3 ⟨
      s (s (s (s z))) ∷= 4 ⟨
      ⟨⟩