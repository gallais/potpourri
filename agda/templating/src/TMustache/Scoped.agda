{-# OPTIONS --guardedness #-}

module TMustache.Scoped where

open import Level using (0ℓ)
open import Data.Bool.Base using (Bool; true; false; not; T; if_then_else_)
open import Data.Bool.Properties using (T?)
open import Data.Product as Prod using (∃; _×_; -,_; _,_; proj₁; proj₂)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
import Data.Maybe.Effectful as Maybe
open import Agda.Builtin.String using () renaming (primStringEquality to _≡ᵇ_)
open import Data.String.Base as String using (String; _++_)

open import Effect.Monad

open import Function.Base using (_$_; id; _on_; _∘_; case_of_)

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

⟦_⟧ty : Type → Set
⟦_⟧sc : Scope → Set

data List⟦_⟧sc (tys : Record Type) : Set where
  [] : List⟦ tys ⟧sc
  _∷_ : ⟦ tys ⟧sc → List⟦ tys ⟧sc → List⟦ tys ⟧sc

⟦ `String   ⟧ty = String
⟦ `Bool     ⟧ty = Bool
⟦ `List tys ⟧ty = List⟦ tys ⟧sc

data ⟦_⟧ : (String × Type) → Set where
  _≔_ : (str : String) {ty : Type} → ⟦ ty ⟧ty → ⟦ str , ty ⟧

⟦ Γ ⟧sc = All ⟦_⟧ Γ

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

scope : {Γ : Scope} (str : String) → Maybe (Mustache Γ)
scope str
  = do rmst ← Raw.mustache str
       checkMustache rmst

instVar : ∀ {str ty Γ} → (str , ty) ∈ Γ → ⟦ Γ ⟧sc → ⟦ ty ⟧ty
instVar (here refl) ((_ ≔ v) ∷ _) = v
instVar (there var) (_ ∷ ρ) = instVar var ρ

instMustache : ∀ {Γ} → Mustache Γ → ⟦ Γ ⟧sc → String
instBlock : ∀ {Γ} → Block Γ → ⟦ Γ ⟧sc → String

instMustache [] ρ = ""
instMustache (blk ∷ mst) ρ = instBlock blk ρ ++ instMustache mst ρ

instBlock (tag var) ρ = instVar var ρ
instBlock (if var then mst) ρ
  = if instVar var ρ then instMustache mst ρ else ""
instBlock (forEach var mst) ρ
  = let ρs = instVar var ρ in
    {!!} -- String.concat (List.map (instMustache mst) ρs)
instBlock (literal str) ρ = str
