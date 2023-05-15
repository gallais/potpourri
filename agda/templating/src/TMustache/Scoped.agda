{-# OPTIONS --guardedness #-}

module TMustache.Scoped where

open import Level using (0ℓ)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Product as Prod using (∃; _×_; -,_; _,_; proj₁; proj₂)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′; maybe)
import Data.Maybe.Effectful as Maybe
open import Agda.Builtin.String using () renaming (primStringEquality to _≡ᵇ_)
open import Data.String.Base as String using (String; _++_)

open import Effect.Monad

open import Function.Base using (_$_; id; _on_; _∘_; const)

open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Records and types

Record : Set → Set
Record A = List (String × A)

data Type : Set where
  `String : Type
  `Bool   : Type
  `List   : Record Type → Type

Scope = Record Type

data ⟦_⟧ : Type → Set
data ⟦_⟧f : (String × Type) → Set
data ⟦_⟧s : List (String × Type) → Set

data ⟦_⟧ where
  AString : String → ⟦ `String ⟧
  false   : ⟦ `Bool ⟧
  true    : ⟦ `Bool ⟧
  []      : ∀ {tys} → ⟦ `List tys ⟧
  _∷_     : ∀ {tys} → ⟦ tys ⟧s → ⟦ `List tys ⟧ → ⟦ `List tys ⟧

data ⟦_⟧f where
  _≔_ : (str : String) {ty : Type} → ⟦ ty ⟧ → ⟦ str , ty ⟧f

data ⟦_⟧s where
  [] : ⟦ [] ⟧s
  _∷_ : ∀ {fld tys} → ⟦ fld ⟧f → ⟦ tys ⟧s → ⟦ fld ∷ tys ⟧s


toBool : ⟦ `Bool ⟧ → Bool
toBool true = true
toBool false = false

toList : ∀ {tys} → ⟦ `List tys ⟧ → List ⟦ tys ⟧s
toList [] = []
toList (v ∷ vs) = v ∷ toList vs

open import Agda.Builtin.FromString public
import Data.String.Literals
open import Data.Unit.Base

instance
  StringIsString = Data.String.Literals.isString
  MeaningIsString : IsString ⟦ `String ⟧
  MeaningIsString .IsString.Constraint str = ⊤
  MeaningIsString .IsString.fromString str = AString str

open import TMustache.Raw as Raw using ()
open Raw.Block

open RawMonad (Maybe.monad {f = 0ℓ})

------------------------------------------------------------------------
-- Contexts and de Bruijn indices

open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)
open import Data.List.Membership.Propositional using (_∈_)

lookup : (str : String) (Γ : Scope) → Maybe (∃ λ ty → (str , ty) ∈ Γ)
lookup str [] = nothing
lookup str ((str′ , ty) ∷ Γ)
  = if str ≡ᵇ str′ then just (ty , here trustMe)
    else Maybe.map (Prod.map₂ there) (lookup str Γ)

------------------------------------------------------------------------
-- Mustache blocks

Mustache : Pred Scope 0ℓ

data Block (Γ : Scope) : Set where
  tag      : ∀ {str} → (str , `String) ∈ Γ → Block Γ
  if_then_ : ∀ {str} → (str , `Bool) ∈ Γ → Mustache Γ → Block Γ
  forEach  : ∀ {str Δ} → (str , `List Δ) ∈ Γ → Mustache Δ → Block Γ
  literal  : String → Block Γ

Mustache Γ = List (Block Γ)

checkBlock : {Γ : Scope} → Raw.Block → Maybe (Block Γ)
checkMustache : {Γ : Scope} → Raw.Mustache → Maybe (Mustache Γ)

checkBlock (tag str)
  = do `String , var ← lookup str _
         where _ → nothing
       pure (tag var)
checkBlock (if str then rmst)
  = do `Bool , var ← lookup str _
         where _ → nothing
       mst ← checkMustache rmst
       pure (if var then mst)
checkBlock (forEach str rmst)
  = do `List Δ , var ← lookup str _
         where _ → nothing
       mst ← checkMustache rmst
       pure (forEach var mst)
checkBlock (literal str) = just (literal str)

checkMustache [] = pure []
checkMustache (rblk ∷ rmst) = ⦇ checkBlock rblk ∷ checkMustache rmst ⦈

data Error : Set where
  error : Error

OrError : {A : Set} → Maybe A → Set
OrError {A} = maybe′ (const A) Error

orError : {A : Set} → (ma : Maybe A) → OrError ma
orError nothing = error
orError (just a) = a

instVar : ∀ {str ty Γ} → (str , ty) ∈ Γ → ⟦ Γ ⟧s → ⟦ ty ⟧
instVar (here refl) (_ ≔ v ∷ _) = v
instVar (there var) (_ ≔ _ ∷ ρ) = instVar var ρ

instMustache : ∀ {Γ} → Mustache Γ → ⟦ Γ ⟧s → String
instBlock : ∀ {Γ} → Block Γ → ⟦ Γ ⟧s → String

instMustache [] ρ = ""
instMustache (blk ∷ mst) ρ = instBlock blk ρ ++ instMustache mst ρ

instBlock (tag var) ρ with AString str ← instVar var ρ = str
instBlock (if var then mst) ρ
  = if (toBool (instVar var ρ)) then instMustache mst ρ else ""
instBlock (forEach var mst) ρ
  = String.concat (List.map (instMustache mst) (toList (instVar var ρ)))
instBlock (literal str) ρ = str

instantiate : ∀ {Γ} → String → ⟦ Γ ⟧s → Maybe String
instantiate {Γ} str ρ
  = do rmst ← Raw.mustache str
       mst ← checkMustache rmst
       pure (instMustache mst ρ)

asTemplate : ∀ {Γ} (str : String) (ρ : ⟦ Γ ⟧s) → OrError (instantiate str ρ)
asTemplate str ρ = orError (instantiate str ρ)
