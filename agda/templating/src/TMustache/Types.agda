module TMustache.Types where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.String.Base using (String)
open import Text.Parser.Position using (Position)

------------------------------------------------------------------------
-- Records and types
-- This is hacky but allows us to write things that look like the original
-- values while keeping the syntax

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

------------------------------------------------------------------------
-- Conversion functions

toBool : ⟦ `Bool ⟧ → Bool
toBool true = true
toBool false = false

fromBool : Bool → ⟦ `Bool ⟧
fromBool true = true
fromBool false = false

toList : ∀ {tys} → ⟦ `List tys ⟧ → List ⟦ tys ⟧s
toList [] = []
toList (v ∷ vs) = v ∷ toList vs

fromList : ∀ {tys} → List ⟦ tys ⟧s → ⟦ `List tys ⟧
fromList [] = []
fromList (v ∷ vs) = v ∷ fromList vs

open import Agda.Builtin.FromString public
import Data.String.Literals
open import Data.Unit.Base using (⊤; tt) public

instance
  StringIsString = Data.String.Literals.isString
  MeaningIsString : IsString ⟦ `String ⟧
  MeaningIsString .IsString.Constraint str = ⊤
  MeaningIsString .IsString.fromString str = AString str

toString : ⟦ `String ⟧ → String
toString (AString str) = str

------------------------------------------------------------------------
-- Error messages


data TypeShape : Set where
  `String `Bool `List : TypeShape

infix 2 expected_got_
data TypeErrorMsg : Set where
  expected_got_ : TypeShape → Type → TypeErrorMsg

data ScopeErrorMsg : Set where
  outOfScope : String → ScopeErrorMsg

infix 1 TypeError_∶_
data ErrorMsg : Set where
  ParseError : Position → ErrorMsg
  ScopeError : ScopeErrorMsg → ErrorMsg
  TypeError_∶_ : String → TypeErrorMsg → ErrorMsg
