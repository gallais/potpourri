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
  module CBT = Con.BelongsTo
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
  open Consumption Pr

  _⊗U_ : {σ τ : ty} (S : LT.Usage σ) (T : LT.Usage τ) → LT.Usage $ σ `⊗ τ 
  [ σ ] ⊗U [ τ ] = [ σ `⊗ τ ]
  [ σ ] ⊗U ] T [ = ] [ σ ]`⊗ T [
  ] S [ ⊗U [ τ ] = ] S `⊗[ τ ] [
  ] S [ ⊗U ] T [ = ] S `⊗ T [

  _isUsed⊗U_ : {σ τ : ty} {S : LT.Usage σ} {T : LT.Usage τ}
               (prS : LTU.isUsed S) (prT : LTU.isUsed T) → LTU.isUsed $ S ⊗U T
  ] prS [ isUsed⊗U ] prT [ = ] prS `⊗ prT [

  _&U[_] : {σ : ty} (S : LT.Usage σ) (τ : ty) → LT.Usage $ σ `& τ
  [ σ ] &U[ τ ] = [ σ `& τ ]
  ] S [ &U[ τ ] = ] S `&[ τ ] [

  [_]&U_ : (σ : ty) {τ : ty} (T : LT.Usage τ) → LT.Usage $ σ `& τ 
  [ σ ]&U [ τ ] = [ σ `& τ ]
  [ σ ]&U ] T [ = ] [ σ ]`& T [

  data ⟨_⟩Usage_ (h : ty) : (σ : ty) → Set where
    ⟨⟩       : ⟨ h ⟩Usage h
    ⟨_⟩`⊗_   : {σ τ : ty} (L : ⟨ h ⟩Usage σ) (R : LT.Usage τ) → ⟨ h ⟩Usage σ `⊗ τ
    ⟨_⟩`&[_] : {σ : ty} (L : ⟨ h ⟩Usage σ) (τ : ty) → ⟨ h ⟩Usage σ `& τ
    _`⊗⟨_⟩   : {σ τ : ty} (L : LT.Usage σ) (R : ⟨ h ⟩Usage τ) → ⟨ h ⟩Usage σ `⊗ τ
    [_]`&⟨_⟩ : (σ : ty) {τ : ty} (R : ⟨ h ⟩Usage τ) → ⟨ h ⟩Usage σ `& τ

  _>>U_ : {h σ : ty} (H : LT.Usage h) (S : ⟨ h ⟩Usage σ) → LT.Usage σ
  H >>U ⟨⟩           = H
  H >>U ⟨ S ⟩`⊗ R    = (H >>U S) ⊗U R
  H >>U ⟨ S ⟩`&[ τ ] = (H >>U S) &U[ τ ]
  H >>U L `⊗⟨ S ⟩    = L ⊗U (H >>U S)
  H >>U [ σ ]`&⟨ S ⟩ = [ σ ]&U (H >>U S)

  infix 3 ⟨_⟩Usages_
  data ⟨_⟩Usages_ : (γ δ : Con ty) → Set where
    ε    : {δ : Con ty} (Δ : LC.Usage δ) → ⟨ ε ⟩Usages δ
    _∙_  : {δ γ : Con ty} (Γ : ⟨ γ ⟩Usages δ) {h σ : ty} (S : ⟨ h ⟩Usage σ) → ⟨ γ ∙ h ⟩Usages δ ∙ σ
    _∙′_ : {δ γ : Con ty} (Γ : ⟨ γ ⟩Usages δ) {σ : ty} (S : LT.Usage σ) → ⟨ γ ⟩Usages δ ∙ σ

  _>>Us_ : {γ δ : Con ty} (Γ : LC.Usage γ) (Δ : ⟨ γ ⟩Usages δ) → LC.Usage δ
  Γ       >>Us ε Δ      = Δ
  (Γ ∙ H) >>Us (Δ ∙ S)  = (Γ >>Us Δ) ∙ (H >>U S)
  Γ       >>Us (Δ ∙′ S) = (Γ >>Us Δ) ∙ S

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

  ⟨_⟩⊙C_ : {h σ : ty} (H : ⟨ h ⟩Usage σ) {S S₁ S₂ : LT.Usage h} (sc : S LAT.Usage.≡ S₁ ⊙ S₂) →
           S >>U H LAT.Usage.≡ S₁ >>U H ⊙ S₂ >>U H
  ⟨ ⟨⟩           ⟩⊙C sc = sc
  ⟨ ⟨ H ⟩`⊗ R    ⟩⊙C sc = ⟨ H ⟩⊙C sc ⊗⊙ LAT.Usage.⊙-refl R
  ⟨ ⟨ H ⟩`&[ τ ] ⟩⊙C sc = (⟨ H ⟩⊙C sc) &⊙[ τ ]
  ⟨ L `⊗⟨ H ⟩    ⟩⊙C sc = LAT.Usage.⊙-refl L ⊗⊙ ⟨ H ⟩⊙C sc
  ⟨ [ σ ]`&⟨ H ⟩ ⟩⊙C sc = [ σ ]&⊙ ⟨ H ⟩⊙C sc

  ⟨_⟩⊙Con_ : {γ δ : Con ty} (Δ : ⟨ γ ⟩Usages δ) {Γ Γ₁ Γ₂ : LC.Usage γ} (sc : Γ LAC.≡ Γ₁ ⊙ Γ₂) →
             Γ >>Us Δ LAC.≡ Γ₁ >>Us Δ ⊙ Γ₂ >>Us Δ 
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

  ⟨_⟩∈U_ : {k : Pr} {h σ : ty} (S : ⟨ h ⟩Usage σ) {H₁ H₂ : LT.Usage h} (var : H₁ BTTU.∋ k ∈ H₂) →
           H₁ >>U S BTTU.∋ k ∈ H₂ >>U S
  ⟨ ⟨⟩           ⟩∈U var = var
  ⟨ ⟨ S ⟩`⊗ R    ⟩∈U var = (⟨ S ⟩∈U var) ∈U⊗ R
  ⟨ ⟨ S ⟩`&[ τ ] ⟩∈U var = (⟨ S ⟩∈U var) ∈U&[ τ ]
  ⟨ L `⊗⟨ S ⟩    ⟩∈U var = L ⊗∈U ⟨ S ⟩∈U var
  ⟨ [ σ ]`&⟨ S ⟩ ⟩∈U var = [ σ ]&∈U ⟨ S ⟩∈U var

  ⟨_⟩∈_ : {k : Pr} {γ δ : Con ty} (Δ : ⟨ γ ⟩Usages δ) {Γ₁ Γ₂ : LC.Usage γ} (var : Γ₁ BTC.∋ k ∈ Γ₂) →
           Γ₁ >>Us Δ BTC.∋ k ∈ Γ₂ >>Us Δ
  ⟨ ε _    ⟩∈ ()
  ⟨ Δ ∙′ S ⟩∈ var     = suc (⟨ Δ ⟩∈ var)
  ⟨ Δ ∙ S  ⟩∈ zro var = zro (⟨ S ⟩∈U var)
  ⟨ Δ ∙ S  ⟩∈ suc var = suc (⟨ Δ ⟩∈ var)

  ⟨_⟩⊢_ : {τ : ty} {γ δ : Con ty} (Δ : ⟨ γ ⟩Usages δ) {Γ₁ Γ₂ : LC.Usage γ} (tm : Γ₁ ⊢ τ ⊣ Γ₂) →
           Γ₁ >>Us Δ ⊢ τ ⊣ Γ₂ >>Us Δ
  ⟨ Δ ⟩⊢ `κ var              = `κ (⟨ Δ ⟩∈ var)
  ⟨ Δ ⟩⊢ (tm₁ `⊗ʳ tm₂)       = (⟨ Δ ⟩⊢ tm₁) `⊗ʳ (⟨ Δ ⟩⊢ tm₂)
  ⟨ Δ ⟩⊢ (tm₁ `&ʳ tm₂ by pr) = (⟨ Δ ⟩⊢ tm₁) `&ʳ ⟨ Δ ⟩⊢ tm₂ by ⟨ Δ ⟩⊙Con pr

  axiom : (σ : ty) → Σ[ S ∈ Cover σ ] LTC.isUsed S × (inj[ ε ∙ σ ] ⊢ σ ⊣ ε ∙ ] S [)
  axiom (`κ k)   = `κ k , `κ k , `κ (zro [ `κ ])
  axiom (σ `⊗ τ) =
    let (S₁ , U₁ , tm₁) = axiom σ
        (S₂ , U₂ , tm₂) = axiom τ
        wkTm₁           = ⟨ ε ε ∙ ⟨ ⟨⟩ ⟩`⊗ [ τ ] ⟩⊢ tm₁
        wkTm₂           = ⟨ ε ε ∙ ( ] S₁ [ `⊗⟨ ⟨⟩ ⟩) ⟩⊢ tm₂
    in S₁ `⊗ S₂ , U₁ `⊗ U₂ , wkTm₁ `⊗ʳ wkTm₂
  axiom (σ `& τ) =
    let (S₁ , U₁ , tm₁) = axiom σ
        (S₂ , U₂ , tm₂) = axiom τ
        wkTm₁           = ⟨ ε ε ∙ ⟨ ⟨⟩ ⟩`&[ τ ] ⟩⊢ tm₁
        wkTm₂           = ⟨ ε ε ∙ [ σ ]`&⟨ ⟨⟩ ⟩ ⟩⊢ tm₂
    in σ `& τ , σ `& τ , wkTm₁ `&ʳ wkTm₂ by (ε ∙ ] ] U₁ [`&] U₂ [  [)


  ⟨_⟩Usages-refl : (γ : Con ty) → ⟨ γ ⟩Usages γ
  ⟨ ε     ⟩Usages-refl = ε ε
  ⟨ γ ∙ σ ⟩Usages-refl = ⟨ γ ⟩Usages-refl ∙ ⟨⟩

  Usages-refl : (γ : Con ty) (Γ : LC.Usage γ) → Γ >>Us ⟨ γ ⟩Usages-refl ≡ Γ
  Usages-refl .ε ε       = Eq.refl
  Usages-refl ._ (Γ ∙ S) rewrite Usages-refl _ Γ = Eq.refl

  split₁ : {σ τ : ty} {γ : Con ty} (var : σ `& τ BelongsTo.∈ γ) → ⟨ split-&₁ var ⟩Usages γ
  split₁ CBT.zro       = ⟨ _ ⟩Usages-refl ∙ ⟨ ⟨⟩ ⟩`&[ _ ]
  split₁ (CBT.suc var) = split₁ var ∙ ⟨⟩

  split₁-eq : {γ : Con ty} {σ τ : ty} (var : σ `& τ BelongsTo.∈ γ) →
              inj[ split-&₁ var ] >>Us split₁ var ≡ inj[ γ ]
  split₁-eq {γ ∙ σ `& τ} CBT.zro rewrite Usages-refl γ (inj[ γ ]) = Eq.refl
  split₁-eq (CBT.suc var)        rewrite split₁-eq var = Eq.refl

  split₁IsUsed : {σ τ : ty} {γ : Con ty} (var : σ `& τ CBT.∈ γ) {Γ : LC.Usage (split-&₁ var)}
                 (pr : LC.isUsed Γ) → LC.isUsed $ Γ >>Us split₁ var
  split₁IsUsed CBT.zro       (prΓ ∙ ] prS [) = Eq.subst LC.isUsed (Eq.sym $ Usages-refl _ _) prΓ ∙ ] prS `&[ _ ] [
  split₁IsUsed (CBT.suc var) (prΓ ∙ prS)     = split₁IsUsed var prΓ ∙ prS

  split₂ : {σ τ : ty} {γ : Con ty} (var : σ `& τ BelongsTo.∈ γ) → ⟨ split-&₂ var ⟩Usages γ
  split₂ CBT.zro       = ⟨ _ ⟩Usages-refl ∙ [ _ ]`&⟨ ⟨⟩ ⟩
  split₂ (CBT.suc var) = split₂ var ∙ ⟨⟩

  split₂-eq : {γ : Con ty} {σ τ : ty} (var : σ `& τ BelongsTo.∈ γ) →
              inj[ split-&₂ var ] >>Us split₂ var ≡ inj[ γ ]
  split₂-eq {γ ∙ σ `& τ} CBT.zro rewrite Usages-refl γ (inj[ γ ]) = Eq.refl
  split₂-eq (CBT.suc var)        rewrite split₂-eq var = Eq.refl

  split₂IsUsed : {σ τ : ty} {γ : Con ty} (var : σ `& τ CBT.∈ γ) {Γ : LC.Usage (split-&₂ var)}
                 (pr : LC.isUsed Γ) → LC.isUsed $ Γ >>Us split₂ var
  split₂IsUsed CBT.zro       (prΓ ∙ ] prS [) = Eq.subst LC.isUsed (Eq.sym $ Usages-refl _ _) prΓ ∙ ] [ _ ]`& prS [
  split₂IsUsed (CBT.suc var) (prΓ ∙ prS)     = split₂IsUsed var prΓ ∙ prS

  isUsed⊙Cov : {σ : ty} {S₁ S₂ : Cover σ} (U₁ : LTC.isUsed S₁) (U₂ : LTC.isUsed S₂) →
               Σ[ S ∈ LT.Cover σ ] LTC.isUsed S × S LAT.Cover.≡ S₁ ⊙ S₂
  isUsed⊙Cov (`κ k) (`κ .k) = `κ k , `κ k , `κ k
  isUsed⊙Cov (S₁ `⊗ T₁) (S₂ `⊗ T₂) =
    let (S , US , Ssc) = isUsed⊙Cov S₁ S₂
        (T , UT , Tsc) = isUsed⊙Cov T₁ T₂
    in S `⊗ T , US `⊗ UT  , Ssc `⊗ Tsc
  isUsed⊙Cov (a `& b) (.a `& .b) = a `& b , a `& b , a `& b
  isUsed⊙Cov (a `& b) (U₂ `&[ .b ]) = a `& b , a `& b , sym `&] U₂ [
  isUsed⊙Cov (a `& b) ([ .a ]`& U₂) = a `& b , a `& b , sym ] U₂ [`&
  isUsed⊙Cov (U₁ `&[ b ]) (a `& .b) = a `& b , a `& b , `&] U₁ [
  isUsed⊙Cov (U₁ `&[ b ]) (U₂ `&[ .b ]) =
    let (S , U , sc) = isUsed⊙Cov U₁ U₂
    in S `&[ b ] , U `&[ b ] , sc `&[ b ]
  isUsed⊙Cov (U₁ `&[ b ]) ([ a ]`& U₂) = a `& b , a `& b , ] U₁ [`&] U₂ [
  isUsed⊙Cov ([ a ]`& U₁) (.a `& b) = a `& b , a `& b , ] U₁ [`&
  isUsed⊙Cov ([ a ]`& U₁) (U₂ `&[ b ]) = a `& b , a `& b , sym ] U₂ [`&] U₁ [
  isUsed⊙Cov ([ a ]`& U₁) ([ .a ]`& U₂) =
    let (S , U , sc) = isUsed⊙Cov U₁ U₂
    in [ a ]`& S , [ a ]`& U , [ a ]`& sc

  isUsed⊙Con : {γ : Con ty} {Γ₁ Γ₂ : LC.Usage γ} (U₁ : LC.isUsed Γ₁) (U₂ : LC.isUsed Γ₂) →
               Σ[ Γ ∈ LC.Usage γ ] LC.isUsed Γ × Γ LAC.≡ Γ₁ ⊙ Γ₂
  isUsed⊙Con ε ε = ε , ε , ε
  isUsed⊙Con (U₁ ∙ ] S₁ [) (U₂ ∙ ] S₂ [) =
    let (Γ , UΓ , Γsc) = isUsed⊙Con U₁ U₂
        (S , US , Ssc) = isUsed⊙Cov S₁ S₂
    in Γ ∙ ] S [ , UΓ ∙ ] US [ , Γsc ∙ ] Ssc [

  open Interleaving

  merge : {γ δ e : Con ty} (mg : γ ≡ δ ⋈ e) (Δ : LC.Usage δ) (E : LC.Usage e) →
          ⟨ δ ⟩Usages γ × ⟨ e ⟩Usages γ
  merge ε         Δ       E       = ε ε , ε ε
  merge (mg ∙ʳ σ) Δ       (E ∙ S) = Prod.map (λ Γ → Γ ∙′ S) (λ Γ → Γ ∙ ⟨⟩) $ merge mg Δ E
  merge (mg ∙ˡ σ) (Δ ∙ S) E       = Prod.map (λ Γ → Γ ∙ ⟨⟩) (λ Γ → Γ ∙′ S) $ merge mg Δ E

  merge-eq : {γ δ e : Con ty} (mg : γ ≡ δ ⋈ e) (Δ : LC.Usage δ) (E : LC.Usage e) →
             let (H₁ , H₂) = merge mg Δ E in E >>Us H₂ ≡ Δ >>Us H₁
  merge-eq ε         Δ       E       = Eq.refl
  merge-eq (mg ∙ʳ σ) Δ       (E ∙ S) = Eq.cong₂ _∙_ (merge-eq mg Δ E) Eq.refl
  merge-eq (mg ∙ˡ σ) (Δ ∙ S) E       = Eq.cong₂ _∙_ (merge-eq mg Δ E) Eq.refl

  merge-inj : {γ δ e : Con ty} (mg : γ ≡ δ ⋈ e) (Δ : LC.Usage δ) →
              inj[ δ ] >>Us proj₁ (merge mg Δ inj[ e ]) ≡ inj[ γ ]
  merge-inj ε         Δ       = Eq.refl
  merge-inj (mg ∙ʳ σ) Δ       = Eq.cong₂ _∙_ (merge-inj mg Δ) Eq.refl
  merge-inj (mg ∙ˡ σ) (Δ ∙ S) = Eq.cong₂ _∙_ (merge-inj mg Δ) Eq.refl

  mergeIsUsed : {γ δ e : Con ty} (mg : γ ≡ δ ⋈ e)
                {Δ : LC.Usage δ} (prΔ : LC.isUsed Δ) {E : LC.Usage e} (prE : LC.isUsed E) →
                LC.isUsed $ E >>Us proj₂ (merge mg Δ inj[ e ])
  mergeIsUsed ε         prΔ         prE         = ε
  mergeIsUsed (mg ∙ʳ σ) prΔ         (prE ∙ prS) = mergeIsUsed mg prΔ prE ∙ prS
  mergeIsUsed (mg ∙ˡ σ) (prΔ ∙ prS) prE         = mergeIsUsed mg prΔ prE ∙ prS

  Usage-split-⊗⁻¹ : {γ : Con ty} {σ τ : ty} (var : σ `⊗ τ CBT.∈ γ) (Γ : LC.Usage $ split-⊗ var) → LC.Usage γ
  Usage-split-⊗⁻¹ CBT.zro       (Γ ∙ S ∙ T) = Γ ∙ (S ⊗U T)
  Usage-split-⊗⁻¹ (CBT.suc var) (Γ ∙ S)     = Usage-split-⊗⁻¹ var Γ ∙ S

  ∋∈-split-⊗⁻¹ : {γ : Con ty} {σ τ : ty} {k : Pr} (var : σ `⊗ τ CBT.∈ γ) {Γ Δ : LC.Usage $ split-⊗ var}
                 (tm : Γ BTC.∋ k ∈ Δ) → Usage-split-⊗⁻¹ var Γ BTC.∋ k ∈ Usage-split-⊗⁻¹ var Δ
  ∋∈-split-⊗⁻¹ CBT.zro {Γ = Γ ∙ S₁ ∙ T₁} (BTC.zro pr) = BTC.zro (S₁ ⊗∈U pr)
  ∋∈-split-⊗⁻¹ CBT.zro       (BTC.suc (BTC.zro pr))   = BTC.zro (pr ∈U⊗ _)
  ∋∈-split-⊗⁻¹ CBT.zro       (BTC.suc (BTC.suc tm))   = BTC.suc tm
  ∋∈-split-⊗⁻¹ (CBT.suc var) (BTC.zro pr)             = BTC.zro pr
  ∋∈-split-⊗⁻¹ (CBT.suc var) (BTC.suc tm)             = BTC.suc (∋∈-split-⊗⁻¹ var tm)

  ⊙-split-⊗⁻¹ : {γ : Con ty} {σ τ : ty} (var : σ `⊗ τ CBT.∈ γ)
                {Γ Γ₁ Γ₂ : LC.Usage $ split-⊗ var} (sc : Γ LAC.≡ Γ₁ ⊙ Γ₂) →
                Usage-split-⊗⁻¹ var Γ LAC.≡ Usage-split-⊗⁻¹ var Γ₁ ⊙ Usage-split-⊗⁻¹ var Γ₂
  ⊙-split-⊗⁻¹ CBT.zro       (sc ∙ scS ∙ scT) = sc ∙ (scS ⊗⊙ scT)
  ⊙-split-⊗⁻¹ (CBT.suc var) (sc ∙ scS)       = ⊙-split-⊗⁻¹ var sc ∙ scS

  ⊢⊣-split-⊗⁻¹ : {γ : Con ty} {σ τ υ : ty} (var : σ `⊗ τ CBT.∈ γ) {Γ Δ : LC.Usage $ split-⊗ var}
                 (tm : Γ ⊢ υ ⊣ Δ) → Usage-split-⊗⁻¹ var Γ ⊢ υ ⊣ Usage-split-⊗⁻¹ var Δ
  ⊢⊣-split-⊗⁻¹ var (`κ pr)             = `κ (∋∈-split-⊗⁻¹ var pr)
  ⊢⊣-split-⊗⁻¹ var (tm₁ `⊗ʳ tm₂)       = ⊢⊣-split-⊗⁻¹ var tm₁ `⊗ʳ ⊢⊣-split-⊗⁻¹ var tm₂
  ⊢⊣-split-⊗⁻¹ var (tm₁ `&ʳ tm₂ by sc) = ⊢⊣-split-⊗⁻¹ var tm₁ `&ʳ ⊢⊣-split-⊗⁻¹ var tm₂ by ⊙-split-⊗⁻¹ var sc

  split-⊗⁻¹-inj : {γ : Con ty} {σ τ : ty} (var : σ `⊗ τ CBT.∈ γ) →
                  Usage-split-⊗⁻¹ var (inj[ split-⊗ var ]) ≡ inj[ γ ]
  split-⊗⁻¹-inj CBT.zro       = Eq.refl
  split-⊗⁻¹-inj (CBT.suc var) = Eq.cong₂ _∙_ (split-⊗⁻¹-inj var) Eq.refl

  split-⊗⁻¹IsUsed : {γ : Con ty} {σ τ : ty} (var : σ `⊗ τ CBT.∈ γ) {Γ : LC.Usage $ split-⊗ var}
                    (pr : LC.isUsed Γ) → LC.isUsed $ Usage-split-⊗⁻¹ var Γ
  split-⊗⁻¹IsUsed CBT.zro       (prΓ ∙ prS ∙ prT) = prΓ ∙ (prS isUsed⊗U prT)
  split-⊗⁻¹IsUsed (CBT.suc var) (prΓ ∙ prS)       = split-⊗⁻¹IsUsed var prΓ ∙ prS

  complete : {γ : Con ty} {σ : ty} (tm : γ ⊢ σ) →
             Σ[ Γ ∈ LC.Usage γ ] (LC.isUsed Γ) × (inj[ γ ] ⊢ σ ⊣ Γ)
  complete {σ = σ} `v          =
    let (S , U , tm) = axiom σ
    in ε ∙ ] S [ , ε ∙ ] U [ , tm
  complete {σ = σ} (var `⊗ˡ tm)        =
    let (Δ , U , tm) = complete tm
        Δ′           = Usage-split-⊗⁻¹ var Δ
        tm′          = Eq.subst (λ Γ → Γ ⊢ σ ⊣ Δ′) (split-⊗⁻¹-inj var) (⊢⊣-split-⊗⁻¹ var tm)
    in Δ′ , split-⊗⁻¹IsUsed var U , tm′
  complete {γ} {σ} (var `&ˡ₁ tm)       =
    let (Γ , U , tm) = complete tm
        Γ′           = Γ >>Us split₁ var
        U′           = split₁IsUsed var U
    in Γ′ , U′ , Eq.subst (λ Γ → Γ ⊢ σ ⊣ Γ′) (split₁-eq var) (⟨ split₁ var ⟩⊢ tm)
  complete {γ} {σ} (var `&ˡ₂ tm)       =
    let (Γ , U , tm) = complete tm
        Γ′           = Γ >>Us split₂ var
        U′           = split₂IsUsed var U
    in Γ′ , U′ , Eq.subst (λ Γ → Γ ⊢ σ ⊣ Γ′) (split₂-eq var) (⟨ split₂ var ⟩⊢ tm)
  complete {γ} {σ `⊗ τ} (tm₁ `⊗ʳ tm₂ by mg) =
    let (Γ₁ , U₁ , tm₁) = complete tm₁
        (Γ₂ , U₂ , tm₂) = complete tm₂
        (H₁ , H₂)       = merge mg Γ₁ inj[ _ ]
        tm₁             = Eq.subst (λ Γ → Γ ⊢ σ ⊣ Γ₁ >>Us H₁) (merge-inj mg Γ₁) (⟨ H₁ ⟩⊢ tm₁)
        tm₂             = Eq.subst (λ Δ → Δ ⊢ τ ⊣ Γ₂ >>Us H₂) (merge-eq mg Γ₁ inj[ _ ]) (⟨ H₂ ⟩⊢ tm₂)
        U               = mergeIsUsed mg U₁ U₂
    in Γ₂ >>Us H₂ , U , tm₁ `⊗ʳ tm₂
  complete (tm₁ `&ʳ tm₂)       =
    let (Γ₁ , U₁ , tm₁) = complete tm₁
        (Γ₂ , U₂ , tm₂) = complete tm₂
        (Γ , U , sc)    = isUsed⊙Con U₁ U₂
    in Γ , U , tm₁ `&ʳ tm₂ by sc


  ⊢-dec : (γ : Con ty) (σ : ty) → Dec $ γ ⊢ σ
  ⊢-dec γ σ with ⊢⊣-dec inj[ γ ] σ
  ... | no ¬p = no (¬p ∘ complete)
  ... | yes (Γ , U , tm) =
    let (E , d , pr) = Soundness.Context.⟦ tm ⟧
    in yes (LC.⟦isUsed⟧ (LCC.isUsed-diff U d) pr)