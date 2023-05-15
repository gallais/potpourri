{-# OPTIONS --guardedness #-}

module TMustache.Scoped where

open import Level using (0ℓ)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Product as Prod using (∃; _×_; -,_; _,_; proj₁; proj₂)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
import Data.Sum.Effectful.Left as Sum
open import Agda.Builtin.String using () renaming (primStringEquality to _≡ᵇ_)
open import Data.String.Base as String using (String; _++_)

open import Effect.Monad

open import Function.Strict
open import Function.Base using (_$_; id; _on_; _∘_; const)

open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Pred)

open import TMustache.Types
open import TMustache.Raw as Raw using ()
open Raw.Block

open RawMonad (Sum.monad ErrorMsg 0ℓ)


------------------------------------------------------------------------
-- Contexts and de Bruijn indices

open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)
open import Data.List.Membership.Propositional using (_∈_)

lookup : (str : String) (Γ : Scope) → ErrorMsg ⊎ (∃ λ ty → (str , ty) ∈ Γ)
lookup str [] = inj₁ (ScopeError (outOfScope str))
lookup str ((str′ , ty) ∷ Γ)
  = if str ≡ᵇ str′ then inj₂ (ty , here trustMe)
    else Sum.map₂ (Prod.map₂ there) (lookup str Γ)

------------------------------------------------------------------------
-- Mustache blocks

Mustache : Pred Scope 0ℓ

data Block (Γ : Scope) : Set where
  tag      : ∀ {str} → (str , `String) ∈ Γ → Block Γ
  if_then_ : ∀ {str} → (str , `Bool) ∈ Γ → Mustache Γ → Block Γ
  forEach  : ∀ {str Δ} → (str , `List Δ) ∈ Γ → Mustache Δ → Block Γ
  literal  : String → Block Γ

Mustache Γ = List (Block Γ)

checkBlock : {Γ : Scope} → Raw.Block → ErrorMsg ⊎ Block Γ
checkMustache : {Γ : Scope} → Raw.Mustache → ErrorMsg ⊎ Mustache Γ

checkBlock (tag str)
  = do `String , var ← lookup str _
         where (ty , _) → inj₁ (TypeError str ∶ expected `String got ty)
       pure (tag var)
checkBlock (if str then rmst)
  = do `Bool , var ← lookup str _
         where (ty , _) → inj₁ (TypeError str ∶ expected `Bool got ty)
       mst ← checkMustache rmst
       pure (if var then mst)
checkBlock (forEach str rmst)
  = do `List Δ , var ← lookup str _
         where (ty , _) → inj₁ (TypeError str ∶ expected `List got ty)
       mst ← checkMustache rmst
       pure (forEach var mst)
checkBlock (literal str) = inj₂ (literal str)

checkMustache [] = pure []
checkMustache (rblk ∷ rmst) = ⦇ checkBlock rblk ∷ checkMustache rmst ⦈

data Error (msg : ErrorMsg) : Set where
  error : Error msg

OrError : {A : Set} → ErrorMsg ⊎ A → Set
OrError {A} = [ Error $!_ , const A ]′

orError : {A : Set} → (ma : ErrorMsg ⊎ A) → OrError ma
orError (inj₁ err) rewrite force-≡ err Error = error
orError (inj₂ val) = val

instVar : ∀ {str ty Γ} → (str , ty) ∈ Γ → ⟦ Γ ⟧s → ⟦ ty ⟧
instVar (here refl) (_ ≔ v ∷ _) = v
instVar (there var) (_ ≔ _ ∷ ρ) = instVar var ρ

instMustache : ∀ {Γ} → Mustache Γ → ⟦ Γ ⟧s → String
instBlock : ∀ {Γ} → Block Γ → ⟦ Γ ⟧s → String

instMustache [] ρ = ""
instMustache (blk ∷ mst) ρ = instBlock blk ρ ++ instMustache mst ρ

instBlock (tag var) ρ = toString (instVar var ρ)
instBlock (if var then mst) ρ
  = if (toBool (instVar var ρ)) then instMustache mst ρ else ""
instBlock (forEach var mst) ρ
  = String.concat (List.map (instMustache mst) (toList (instVar var ρ)))
instBlock (literal str) ρ = str

instantiate : ∀ {Γ} → String → ⟦ Γ ⟧s → ErrorMsg ⊎ String
instantiate {Γ} str ρ
  = do rmst ← Raw.mustache str
       mst ← checkMustache rmst
       pure (instMustache mst ρ)

asTemplate : ∀ {Γ} (str : String) (ρ : ⟦ Γ ⟧s) → OrError (instantiate str ρ)
asTemplate str ρ = orError (instantiate str ρ)
