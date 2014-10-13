import lps.IMLL                  as IMLL
import lps.Linearity             as Linearity
import lps.Linearity.Action      as Action
import lps.Linearity.Consumption as Consumption
import lps.Search.BelongsTo      as BelongsTo
import lps.Search.Calculus       as Calculus

import lib.Context               as Con
open import lib.Maybe
open import lib.Nullary

open import Data.Empty
open import Data.Product as Prod hiding (map)
open import Data.Nat as ℕ
open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module lps.Equivalence (Pr : Set) (_≟_ : (x y : Pr) → Dec (x ≡ y)) where

  module BT = BelongsTo Pr _≟_
  open Con
  open Context
  open Pointwise
  open IMLL Pr
  open IMLL.Type Pr
  open Linearity Pr
  open Linearity.Context Pr
  open Calculus Pr _≟_
  open Calculus.Calculus Pr _≟_
  module BTTU = BT.Type.Usage
  open BT.Context
  open Linearity.Type Pr
  open Linearity.Type.Usage Pr
  open Linearity.Type.Cover Pr
  open Action Pr
  open Action.Context Pr
  open Action.Type.Usage Pr
  open Action.Type.Cover Pr

  _⊗U_ : {σ τ : ty} (S : LT.Usage σ) (T : LT.Usage τ) → LT.Usage $ σ `⊗ τ 
  [ σ ] ⊗U [ τ ] = [ σ `⊗ τ ]
  [ σ ] ⊗U ] T [ = ] [ σ ]`⊗ T [
  ] S [ ⊗U [ τ ] = ] S `⊗[ τ ] [
  ] S [ ⊗U ] T [ = ] S `⊗ T [

  _&U[_] : {σ : ty} (S : LT.Usage σ) (τ : ty) → LT.Usage $ σ `& τ
  [ σ ] &U[ τ ] = [ σ `& τ ]
  ] S [ &U[ τ ] = ] S `&[ τ ] [

  [_]&U_ : (σ : ty) {τ : ty} (T : LT.Usage τ) → LT.Usage $ σ `& τ 
  [ σ ]&U [ τ ] = [ σ `& τ ]
  [ σ ]&U ] T [ = ] [ σ ]`& T [

  data ⟨_⟩Cover_ (h : ty) : (σ : ty) → Set where
    ⟨⟩       : ⟨ h ⟩Cover h
    ⟨_⟩`⊗_   : {σ τ : ty} (L : ⟨ h ⟩Cover σ) (R : Cover τ) → ⟨ h ⟩Cover σ `⊗ τ
    ⟨_⟩`⊗[_] : {σ : ty} (L : ⟨ h ⟩Cover σ) (τ : ty) → ⟨ h ⟩Cover σ `⊗ τ
    ⟨_⟩`&[_] : {σ : ty} (L : ⟨ h ⟩Cover σ) (τ : ty) → ⟨ h ⟩Cover σ `& τ
    _`⊗⟨_⟩   : {σ τ : ty} (L : Cover σ) (R : ⟨ h ⟩Cover τ) → ⟨ h ⟩Cover σ `⊗ τ
    [_]`⊗⟨_⟩ : (σ : ty) {τ : ty} (R : ⟨ h ⟩Cover τ) → ⟨ h ⟩Cover σ `⊗ τ
    [_]`&⟨_⟩ : (σ : ty) {τ : ty} (R : ⟨ h ⟩Cover τ) → ⟨ h ⟩Cover σ `& τ

  _>>C_ : {h σ : ty} (H : LT.Usage h) (S : ⟨ h ⟩Cover σ) → LT.Usage σ
  H >>C ⟨⟩           = H
  H >>C ⟨ S ⟩`⊗ T    = (H >>C S) ⊗U ] T [
  H >>C ⟨ S ⟩`⊗[ τ ] = (H >>C S) ⊗U [ τ ]
  H >>C ⟨ S ⟩`&[ τ ] = (H >>C S) &U[ τ ]
  H >>C S `⊗⟨ T ⟩    = ] S [ ⊗U (H >>C T)
  H >>C [ σ ]`⊗⟨ T ⟩ = [ σ ] ⊗U (H >>C T)
  H >>C [ σ ]`&⟨ T ⟩ = [ σ ]&U (H >>C T)

  infix 3 ⟨_⟩Usage_
  data ⟨_⟩Usage_ : (γ δ : Con ty) → Set where
    ε    : {δ : Con ty} (Δ : LC.Usage δ) → ⟨ ε ⟩Usage δ
    _∙_  : {δ γ : Con ty} (Γ : ⟨ γ ⟩Usage δ) {h σ : ty} (S : ⟨ h ⟩Cover σ) → ⟨ γ ∙ h ⟩Usage δ ∙ σ
    _∙′_ : {δ γ : Con ty} (Γ : ⟨ γ ⟩Usage δ) {σ : ty} (S : LT.Usage σ) → ⟨ γ ⟩Usage δ ∙ σ


  _>>U_ : {γ δ : Con ty} (Γ : LC.Usage γ) (Δ : ⟨ γ ⟩Usage δ) → LC.Usage δ
  Γ       >>U ε Δ      = Δ
  (Γ ∙ H) >>U (Δ ∙ S)  = (Γ >>U Δ) ∙ (H >>C S)
  Γ       >>U (Δ ∙′ S) = (Γ >>U Δ) ∙ S

  _⊗⊙_ : {a b : ty} {A A₁ A₂ : LT.Usage a} {B B₁ B₂ : LT.Usage b}
         (sca : A LAT.Usage.≡ A₁ ⊙ A₂) (scb : B LAT.Usage.≡ B₁ ⊙ B₂) →
         A ⊗U B LAT.Usage.≡ A₁ ⊗U B₁ ⊙ A₂ ⊗U B₂
  [ σ ]   ⊗⊙ [ τ ]   = [ σ `⊗ τ ]
  [ σ ]   ⊗⊙ ] prT [ = ] σ `⊗[ prT ] [
  ] prS [ ⊗⊙ [ τ ]   = ] [ prS ]`⊗ τ [
  ] prS [ ⊗⊙ ] prT [ = ] prS `⊗ prT [

  _&⊙[_] : {a : ty} {A A₁ A₂ : LT.Usage a} (sca : A LAT.Usage.≡ A₁ ⊙ A₂) (b : ty) →
           A &U[ b ] LAT.Usage.≡ A₁ &U[ b ] ⊙ A₂ &U[ b ]
  [ σ ]   &⊙[ τ ] = [ σ `& τ ]
  ] prS [ &⊙[ τ ] = ] prS `&[ τ ] [

  [_]&⊙_ : (a : ty) {b : ty} {B B₁ B₂ : LT.Usage b} (scb : B LAT.Usage.≡ B₁ ⊙ B₂) →
           [ a ]&U B LAT.Usage.≡ [ a ]&U B₁ ⊙ [ a ]&U B₂
  [ σ ]&⊙ [ τ ]   = [ σ `& τ ]
  [ σ ]&⊙ ] prT [ = ] [ σ ]`& prT [

  ⟨_⟩⊙C_ : {h σ : ty} (H : ⟨ h ⟩Cover σ) {S S₁ S₂ : LT.Usage h} (sc : S LAT.Usage.≡ S₁ ⊙ S₂) →
           S >>C H LAT.Usage.≡ S₁ >>C H ⊙ S₂ >>C H
  ⟨ ⟨⟩           ⟩⊙C sc = sc
  ⟨ ⟨ H ⟩`⊗ R    ⟩⊙C sc = ⟨ H ⟩⊙C sc ⊗⊙ LAT.Usage.⊙-refl ] R [
  ⟨ ⟨ H ⟩`⊗[ τ ] ⟩⊙C sc = ⟨ H ⟩⊙C sc ⊗⊙ LAT.Usage.⊙-refl [ τ ]
  ⟨ ⟨ H ⟩`&[ τ ] ⟩⊙C sc = (⟨ H ⟩⊙C sc) &⊙[ τ ]
  ⟨ L `⊗⟨ H ⟩    ⟩⊙C sc = LAT.Usage.⊙-refl ] L [ ⊗⊙ ⟨ H ⟩⊙C sc
  ⟨ [ σ ]`⊗⟨ H ⟩ ⟩⊙C sc = LAT.Usage.⊙-refl [ σ ] ⊗⊙ ⟨ H ⟩⊙C sc
  ⟨ [ σ ]`&⟨ H ⟩ ⟩⊙C sc = [ σ ]&⊙ ⟨ H ⟩⊙C sc

  ⟨_⟩⊙Con_ : {γ δ : Con ty} (Δ : ⟨ γ ⟩Usage δ) {Γ Γ₁ Γ₂ : LC.Usage γ} (sc : Γ LAC.≡ Γ₁ ⊙ Γ₂) →
             Γ >>U Δ LAC.≡ Γ₁ >>U Δ ⊙ Γ₂ >>U Δ 
  ⟨ Δ ∙′ S ⟩⊙Con sc        = ⟨ Δ ⟩⊙Con sc ∙ LAT.Usage.⊙-refl S
  ⟨ ε Δ    ⟩⊙Con ε         = LAC.⊙-refl Δ
  ⟨ Δ ∙ S  ⟩⊙Con (sc ∙ pr) = ⟨ Δ ⟩⊙Con sc ∙ ⟨ S ⟩⊙C pr

  open BT.Type.Cover.FromDented
  open BT.Type.Cover.FromFree
  open BTTU

  _∈U⊗_ : {k : Pr} {σ τ : ty} {S₁ S₂ : LT.Usage σ} (var : S₁ BTTU.∋ k ∈ S₂) (T : LT.Usage τ) →
          S₁ ⊗U T BTTU.∋ k ∈ S₂ ⊗U T
  [ prS ] ∈U⊗ [ τ ] = [ prS `⊗ˡ τ ]
  [ prS ] ∈U⊗ ] T [ = ] [ prS ]`⊗ˡ T [
  ] prS [ ∈U⊗ [ τ ] = ] prS `⊗[ τ ] [
  ] prS [ ∈U⊗ ] T [ = ] prS `⊗ˡ T [

  _∈U&[_] : {k : Pr} {σ : ty} {S₁ S₂ : LT.Usage σ} (var : S₁ BTTU.∋ k ∈ S₂) (τ : ty) →
          S₁ &U[ τ ] BTTU.∋ k ∈ S₂ &U[ τ ]
  [ prS ] ∈U&[ τ ] = [ prS `&ˡ τ ]
  ] prS [ ∈U&[ τ ] = ] prS `&ˡ τ [

  _⊗∈U_ : {k : Pr} {σ : ty} (S : LT.Usage σ) {τ : ty} {T₁ T₂ : LT.Usage τ} (var : T₁ BTTU.∋ k ∈ T₂) →
          S ⊗U T₁ BTTU.∋ k ∈ S ⊗U T₂
  [ σ ] ⊗∈U [ var ] = [ σ `⊗ʳ var ]
  [ σ ] ⊗∈U ] var [ = ] [ σ ]`⊗ var [
  ] S [ ⊗∈U [ var ] = ] S `⊗ʳ[ var ] [
  ] S [ ⊗∈U ] var [ = ] S `⊗ʳ var [

  [_]&∈U_ : {k : Pr} (σ : ty) {τ : ty} {T₁ T₂ : LT.Usage τ} (var : T₁ BTTU.∋ k ∈ T₂) →
          [ σ ]&U T₁ BTTU.∋ k ∈ [ σ ]&U T₂
  [ σ ]&∈U [ var ] = [ σ `&ʳ var ]
  [ σ ]&∈U ] var [ = ] σ `&ʳ var [

  ⟨_⟩∈U_ : {k : Pr} {h σ : ty} (S : ⟨ h ⟩Cover σ) {H₁ H₂ : LT.Usage h} (var : H₁ BTTU.∋ k ∈ H₂) →
           H₁ >>C S BTTU.∋ k ∈ H₂ >>C S
  ⟨ ⟨⟩           ⟩∈U var = var
  ⟨ ⟨ S ⟩`⊗ R    ⟩∈U var = (⟨ S ⟩∈U var) ∈U⊗ ] R [
  ⟨ ⟨ S ⟩`⊗[ τ ] ⟩∈U var = (⟨ S ⟩∈U var) ∈U⊗ [ τ ]
  ⟨ ⟨ S ⟩`&[ τ ] ⟩∈U var = (⟨ S ⟩∈U var) ∈U&[ τ ]
  ⟨ L `⊗⟨ S ⟩    ⟩∈U var = ] L [ ⊗∈U ⟨ S ⟩∈U var
  ⟨ [ σ ]`⊗⟨ S ⟩ ⟩∈U var = [ σ ] ⊗∈U ⟨ S ⟩∈U var
  ⟨ [ σ ]`&⟨ S ⟩ ⟩∈U var = [ σ ]&∈U ⟨ S ⟩∈U var

  ⟨_⟩∈_ : {k : Pr} {γ δ : Con ty} (Δ : ⟨ γ ⟩Usage δ) {Γ₁ Γ₂ : LC.Usage γ} (var : Γ₁ BTC.∋ k ∈ Γ₂) →
           Γ₁ >>U Δ BTC.∋ k ∈ Γ₂ >>U Δ
  ⟨ ε _    ⟩∈ ()
  ⟨ Δ ∙′ S ⟩∈ var     = suc (⟨ Δ ⟩∈ var)
  ⟨ Δ ∙ S  ⟩∈ zro var = zro (⟨ S ⟩∈U var)
  ⟨ Δ ∙ S  ⟩∈ suc var = suc (⟨ Δ ⟩∈ var)

  ⟨_⟩⊢_ : {τ : ty} {γ δ : Con ty} (Δ : ⟨ γ ⟩Usage δ) {Γ₁ Γ₂ : LC.Usage γ} (tm : Γ₁ ⊢ τ ⊣ Γ₂) →
           Γ₁ >>U Δ ⊢ τ ⊣ Γ₂ >>U Δ
  ⟨ Δ ⟩⊢ `κ var              = `κ (⟨ Δ ⟩∈ var)
  ⟨ Δ ⟩⊢ (tm₁ `⊗ʳ tm₂)       = (⟨ Δ ⟩⊢ tm₁) `⊗ʳ (⟨ Δ ⟩⊢ tm₂)
  ⟨ Δ ⟩⊢ (tm₁ `&ʳ tm₂ by pr) = (⟨ Δ ⟩⊢ tm₁) `&ʳ ⟨ Δ ⟩⊢ tm₂ by ⟨ Δ ⟩⊙Con pr


  axiom : (σ : ty) → Σ[ S ∈ Cover σ ] LTC.isUsed S × (inj[ ε ∙ σ ] ⊢ σ ⊣ ε ∙ ] S [)
  axiom (`κ k)   = `κ k , `κ k , `κ (zro [ `κ ])
  axiom (σ `⊗ τ) =
    let (S₁ , U₁ , tm₁) = axiom σ
        (S₂ , U₂ , tm₂) = axiom τ
        wkTm₁           = ⟨ ε ε ∙ ⟨ ⟨⟩ ⟩`⊗[ τ ] ⟩⊢ tm₁
        wkTm₂           = ⟨ ε ε ∙ ( S₁ `⊗⟨ ⟨⟩ ⟩) ⟩⊢ tm₂
    in S₁ `⊗ S₂ , U₁ `⊗ U₂ , wkTm₁ `⊗ʳ wkTm₂
  axiom (σ `& τ) =
    let (S₁ , U₁ , tm₁) = axiom σ
        (S₂ , U₂ , tm₂) = axiom τ
        wkTm₁           = ⟨ ε ε ∙ ⟨ ⟨⟩ ⟩`&[ τ ] ⟩⊢ tm₁
        wkTm₂           = ⟨ ε ε ∙ [ σ ]`&⟨ ⟨⟩ ⟩ ⟩⊢ tm₂
    in σ `& τ , σ `& τ , wkTm₁ `&ʳ wkTm₂ by (ε ∙ ] ] U₁ [`&] U₂ [  [)


  complete : {γ : Con ty} {σ : ty} (tm : γ ⊢ σ) →
             Σ[ Γ ∈ LC.Usage γ ] (LC.isUsed Γ) × (inj[ γ ] ⊢ σ ⊣ Γ)
  complete {σ = σ} `v          =
    let (S , U , tm) = axiom σ
    in ε ∙ ] S [ , ε ∙ ] U [ , tm
  complete (var `⊗ˡ tm)        = {!!}
  complete (var `&ˡ₁ tm)       = {!!}
  complete (var `&ˡ₂ tm)       = {!!}
  complete (tm₁ `⊗ʳ tm₂ by mg) = {!!}
  complete (tm₁ `&ʳ tm₂)       =
    let (Γ₁ , U₁ , tm₁) = complete tm₁
        (Γ₂ , U₂ , tm₂) = complete tm₂
    in {!!}
