import lps.IMLL                  as IMLL
import lps.Linearity             as Linearity
import lps.Linearity.Consumption as Consumption

open import Data.Empty
open import Data.Product hiding (map)
open import Function

import lib.Context as Con
module BT = Con.BelongsTo
module BTT = BT.BelongsTo

open import lib.Maybe
open import lib.Nullary

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module lps.Search.BelongsTo (Pr : Set) (_≟_ : (x y : Pr) → Dec (x ≡ y)) where

  module Type where

    open Con.Context
    open IMLL.Type Pr

    module Cover where

      open Linearity.Type Pr

      module FromFree where

        infix 4 _∈[_]▸_
        data _∈[_]▸_ (k : Pr) : (σ : ty) (S : Cover σ) → Set where
          `κ    : k ∈[ `κ k ]▸ `κ k
          _`&ˡ_ : {σ : ty} {S : Cover σ} (prS : k ∈[ σ ]▸ S) (τ : ty) →
                  k ∈[ σ `& τ ]▸ S `&[ τ ]
          _`&ʳ_ : (σ : ty) {τ : ty} {T : Cover τ} (prT : k ∈[ τ ]▸ T) →
                  k ∈[ σ `& τ ]▸ [ σ ]`& T
          _`⊗ˡ_ : {σ : ty} {S : Cover σ} (prS : k ∈[ σ ]▸ S) (τ : ty) →
                  k ∈[ σ `⊗ τ ]▸ S `⊗[ τ ]
          _`⊗ʳ_ : (σ : ty) {τ : ty} {T : Cover τ} (prT : k ∈[ τ ]▸ T) →
                  k ∈[ σ `⊗ τ ]▸ [ σ ]`⊗ T

        infix 4 [_]∋_∈_
        [_]∋_∈_ : (σ : ty) (k : Pr) (T : Cover σ) → Set
        [ σ ]∋ k ∈ τ = k ∈[ σ ]▸ τ

        ∈κ : ∀ k {l} → k ≡ l → Σ[ C ∈ Cover $ `κ l ] [ `κ l ]∋ k ∈ C
        ∈κ k Eq.refl = `κ k , `κ

        ∈[&]ˡ : ∀ {k σ} (τ : ty) → Σ[ S ∈ Cover σ ] [ σ ]∋ k ∈ S →
                Σ[ ST ∈ Cover $ σ `& τ ] [ σ `& τ ]∋ k ∈ ST
        ∈[&]ˡ τ (S , prS) = S `&[ τ ] , prS `&ˡ τ

        ∈[&]ʳ : ∀ {k τ} (σ : ty) → Σ[ T ∈ Cover τ ] [ τ ]∋ k ∈ T →
                Σ[ ST ∈ Cover $ σ `& τ ] [ σ `& τ ]∋ k ∈ ST
        ∈[&]ʳ σ (T , prT) = [ σ ]`& T , σ `&ʳ prT

        ∈[⊗]ˡ : ∀ {k σ} (τ : ty) → Σ[ S ∈ Cover σ ] [ σ ]∋ k ∈ S →
                Σ[ ST ∈ Cover $ σ `⊗ τ ] [ σ `⊗ τ ]∋ k ∈ ST
        ∈[⊗]ˡ τ (S , prS) = S `⊗[ τ ] , prS `⊗ˡ τ

        ∈[⊗]ʳ : ∀ {k τ} (σ : ty) → Σ[ T ∈ Cover τ ] [ τ ]∋ k ∈ T →
                Σ[ ST ∈ Cover $ σ `⊗ τ ] [ σ `⊗ τ ]∋ k ∈ ST
        ∈[⊗]ʳ σ (T , prT) = [ σ ]`⊗ T , σ `⊗ʳ prT


        open Context
        infix 6 _∈?[_]
        _∈?[_] : (k : Pr) (σ : ty) → Con (Σ[ S′ ∈ Cover σ ] [ σ ]∋ k ∈ S′)
        k ∈?[ `κ l   ] = dec (k ≟ l) (return ∘ ∈κ k) (const ε)
        k ∈?[ σ `⊗ τ ] = map (∈[⊗]ˡ τ) (k ∈?[ σ ]) ++ map (∈[⊗]ʳ σ) (k ∈?[ τ ])
        k ∈?[ σ `& τ ] = map (∈[&]ˡ τ) (k ∈?[ σ ]) ++ map (∈[&]ʳ σ) (k ∈?[ τ ])


        ∈?[]-complete : (k : Pr) (σ : ty) {T : Cover σ} (pr : [ σ ]∋ k ∈ T) →
                        (T , pr) BT.∈ k ∈?[ σ ]
        ∈?[]-complete k (`κ l)   pr with k ≟ l
        ∈?[]-complete k (`κ .k) `κ | yes Eq.refl = BT.zro
        ∈?[]-complete k (`κ .k) `κ | no ¬eq      = ⊥-elim $ ¬eq Eq.refl
        ∈?[]-complete k (σ `⊗ τ) (pr `⊗ˡ .τ) = BTT.∈++ˡ (map (∈[⊗]ʳ σ) (k ∈?[ τ ]))
                                                        (BTT.map (∈[⊗]ˡ τ) (∈?[]-complete k σ pr))
        ∈?[]-complete k (σ `⊗ τ) (.σ `⊗ʳ pr) = BTT.∈++ʳ (BTT.map (∈[⊗]ʳ σ) (∈?[]-complete k τ pr))
        ∈?[]-complete k (σ `& τ) (pr `&ˡ .τ) = BTT.∈++ˡ (map (∈[&]ʳ σ) (k ∈?[ τ ]))
                                                        (BTT.map (∈[&]ˡ τ) (∈?[]-complete k σ pr))
        ∈?[]-complete k (σ `& τ) (.σ `&ʳ pr) = BTT.∈++ʳ (BTT.map (∈[&]ʳ σ) (∈?[]-complete k τ pr))

        open IMLL Pr
        open Linearity.LTC Pr
        ⟦_⟧ : {σ : ty} {k : Pr} {T : Cover σ} (pr : [ σ ]∋ k ∈ T) → ｢ T ｣ ⊢ `κ k
        ⟦ `κ       ⟧ = `v
        ⟦ pr `&ˡ τ ⟧ = ⟦ pr ⟧
        ⟦ σ `&ʳ pr ⟧ = ⟦ pr ⟧
        ⟦ pr `⊗ˡ τ ⟧ = ⟦ pr ⟧
        ⟦ σ `⊗ʳ pr ⟧ = ⟦ pr ⟧

      module FromDented where

        open FromFree hiding (⟦_⟧)

        infix 4 _∈_▸_
        data _∈_▸_ (k : Pr) : {σ : ty} (S : Cover σ) (T : Cover σ) → Set where
          _`⊗ˡ_   : {σ : ty} {S S′ : Cover σ} (s : k ∈ S ▸ S′)
                    {τ : ty} (T : Cover τ) → k ∈ S `⊗ T ▸ S′ `⊗ T
          _`⊗ʳ_   : {σ : ty} (S : Cover σ) {τ : ty} {T T′ : Cover τ}
                    (t : k ∈ T ▸ T′) → k ∈ S `⊗ T ▸ S `⊗ T′
          [_]`⊗_  : (σ : ty) {τ : ty} {T T′ : Cover τ} (t : k ∈ T ▸ T′) →
                    k ∈ [ σ ]`⊗ T ▸ [ σ ]`⊗ T′
          _`⊗ʳ[_] : {σ : ty} (S : Cover σ) {τ : ty} {T : Cover τ}
                    (prT : k ∈[ τ ]▸ T) → k ∈ S `⊗[ τ ] ▸ S `⊗ T
          [_]`⊗ˡ_ : {σ : ty} {S : Cover σ} (prS : k ∈[ σ ]▸ S)
                    {τ : ty} (T : Cover τ)  → k ∈ [ σ ]`⊗ T ▸ S `⊗ T
          _`⊗[_]  : {σ : ty} {S S′ : Cover σ} (s : k ∈ S ▸ S′) (τ : ty) →
                    k ∈ S `⊗[ τ ] ▸ S′ `⊗[ τ ]
          _`&ˡ_   : ∀ {σ} {S S′ : Cover σ} (s : k ∈ S ▸ S′) τ →
                    k ∈ S `&[ τ ] ▸ S′ `&[ τ ]
          _`&ʳ_   : ∀ σ {τ} {T T′ : Cover τ} (t : k ∈ T ▸ T′) →
                    k ∈ [ σ ]`& T ▸ [ σ ]`& T′

        infix 4 _∋_∈_
        _∋_∈_ : {σ : ty} (S : Cover σ) (k : Pr) (T : Cover σ) → Set
        σ ∋ k ∈ τ = k ∈ σ ▸ τ

        ∈⊗ˡ : ∀ {k a b} {A : Cover a} (B : Cover b) →
              Σ[ A′ ∈ Cover a ] A ∋ k ∈ A′ →
              Σ[ AB ∈ Cover $ a `⊗ b ] A `⊗ B ∋ k ∈ AB
        ∈⊗ˡ B (A′ , prA) = A′ `⊗ B , prA `⊗ˡ B
  
        ∈⊗ʳ : ∀ {k a b} (A : Cover a) {B : Cover b} →
              Σ[ B′ ∈ Cover b ] B ∋ k ∈ B′ →
              Σ[ AB ∈ Cover $ a `⊗ b ] A `⊗ B ∋ k ∈ AB
        ∈⊗ʳ A (B′ , prB) = A `⊗ B′ , A `⊗ʳ prB

        ∈[]⊗ : ∀ {k : Pr} {b : ty} {B : Cover b} (a : ty) →
               Σ[ B′ ∈ Cover b ] B ∋ k ∈ B′ →
               Σ[ AB ∈ Cover $ a `⊗ b ] [ a ]`⊗ B ∋ k ∈ AB
        ∈[]⊗ a (B′ , prB) = [ a ]`⊗ B′ , [ a ]`⊗ prB

        ∈[]⊗ˡ : ∀ {k : Pr} {b : ty} (B : Cover b) {a : ty} →
                Σ[ A ∈ Cover a ] [ a ]∋ k ∈ A →
                Σ[ AB ∈ Cover $ a `⊗ b ] [ a ]`⊗ B ∋ k ∈ AB
        ∈[]⊗ˡ B (A , prA) = A `⊗ B , [ prA ]`⊗ˡ B

        ∈⊗[] : ∀ {k : Pr} {a : ty} {A : Cover a} (b : ty) →
               Σ[ A′ ∈ Cover a ] A ∋ k ∈ A′ →
               Σ[ AB ∈ Cover $ a `⊗ b ] A `⊗[ b ] ∋ k ∈ AB
        ∈⊗[] b (A′ , prA) = A′ `⊗[ b ] , prA `⊗[ b ]

        ∈⊗[]ʳ : ∀ {k : Pr} {a : ty} (A : Cover a) {b : ty} →
                Σ[ B ∈ Cover b ] [ b ]∋ k ∈ B →
                Σ[ AB ∈ Cover $ a `⊗ b ] A `⊗[ b ] ∋ k ∈ AB
        ∈⊗[]ʳ A (B , prB) = A `⊗ B , A `⊗ʳ[ prB ]
  
        ∈[]& : ∀ {k : Pr} {b : ty} {B : Cover b} (a : ty) →
               Σ[ B′ ∈ Cover b ] B ∋ k ∈ B′ →
               Σ[ AB ∈ Cover $ a `& b ] [ a ]`& B ∋ k ∈ AB
        ∈[]& a (B′ , prB) = [ a ]`& B′ , a `&ʳ prB

        ∈&[] : ∀ {k : Pr} {a : ty} {A : Cover a} (b : ty) →
               Σ[ A′ ∈ Cover a ] A ∋ k ∈ A′ →
               Σ[ AB ∈ Cover $ a `& b ] A `&[ b ] ∋ k ∈ AB
        ∈&[] b (A′ , prA) = A′ `&[ b ] , prA `&ˡ b
        open Context

        infix 6 _∈?_
        _∈?_ : (k : Pr) {σ : ty} (S : Cover σ) → Con (Σ[ S′ ∈ Cover σ ] S ∋ k ∈ S′)
        k ∈? `κ l      = ε
        k ∈? A `⊗ B    = map (∈⊗ˡ B) (k ∈? A) ++ map (∈⊗ʳ A) (k ∈? B)
        k ∈? [ a ]`⊗ B = map (∈[]⊗ˡ B) (k ∈?[ a ]) ++ map (∈[]⊗ a) (k ∈? B)
        k ∈? A `⊗[ b ] = map (∈⊗[] b) (k ∈? A) ++ map (∈⊗[]ʳ A) (k ∈?[ b ])
        k ∈? a `& b    = ε
        k ∈? A `&[ b ] = map (∈&[] b) (k ∈? A)
        k ∈? [ a ]`& B = map (∈[]& a) (k ∈? B)

        ∈?-complete : (k : Pr) {σ : ty} (S : Cover σ) {T : Cover σ} (pr : S ∋ k ∈ T) →
                      (T , pr) BT.∈ k ∈? S
        ∈?-complete k (`κ l)      ()
        ∈?-complete k (S `⊗ T)    (pr `⊗ˡ .T)    = BTT.∈++ˡ (map (∈⊗ʳ S) (k ∈? T))
                                                            (BTT.map (∈⊗ˡ T) (∈?-complete k S pr))
        ∈?-complete k (S `⊗ T)    (.S `⊗ʳ pr)    = BTT.∈++ʳ (BTT.map (∈⊗ʳ S) (∈?-complete k T pr))
        ∈?-complete k ([ σ ]`⊗ T) ([ .σ ]`⊗ pr)  = BTT.∈++ʳ (BTT.map (∈[]⊗ σ) (∈?-complete k T pr))
        ∈?-complete k ([ σ ]`⊗ T) ([ pr ]`⊗ˡ .T) = BTT.∈++ˡ (map (∈[]⊗ σ) (k ∈? T))
                                                            (BTT.map (∈[]⊗ˡ T) (∈?[]-complete k σ pr))
        ∈?-complete k (S `⊗[ τ ]) (.S `⊗ʳ[ pr ]) = BTT.∈++ʳ (BTT.map (∈⊗[]ʳ S) (∈?[]-complete k τ pr))
        ∈?-complete k (S `⊗[ τ ]) (pr `⊗[ .τ ])  = BTT.∈++ˡ (map (∈⊗[]ʳ S) (k ∈?[ τ ]))
                                                            (BTT.map (∈⊗[] τ) (∈?-complete k S pr))
        ∈?-complete k (σ `& τ) ()
        ∈?-complete k (S `&[ τ ]) (pr `&ˡ .τ)    = BTT.map (∈&[] τ) (∈?-complete k S pr)
        ∈?-complete k ([ σ ]`& T) (.σ `&ʳ pr)    = BTT.map (∈[]& σ) (∈?-complete k T pr)

        open IMLL Pr
        open Linearity.LTC Pr
        open Consumption.LCT.Cover Pr

        ⟦⊗ˡ⟧ : ∀ {σ k} τ {S₁ S₂ : Cover σ} (T : Cover τ) →
               Σ[ S ∈ Cover σ ] S₂ ≡ S₁ ─ S × ｢ S ｣ ⊢ `κ k →
               Σ[ ST ∈ Cover $ σ `⊗ τ ] S₂ `⊗ T ≡ S₁ `⊗ T ─ ST × ｢ ST ｣ ⊢ `κ k
        ⟦⊗ˡ⟧ τ T (S , diff , tm) = S `⊗[ τ ] , diff `⊗ˡ T , tm

        ⟦⊗ʳ⟧ : ∀ σ {τ k} (S : Cover σ) {T₁ T₂ : Cover τ} →
               Σ[ T ∈ Cover τ ] T₂ ≡ T₁ ─ T × ｢ T ｣ ⊢ `κ k →
               Σ[ ST ∈ Cover $ σ `⊗ τ ] S `⊗ T₂ ≡ S `⊗ T₁ ─ ST × ｢ ST ｣ ⊢ `κ k
        ⟦⊗ʳ⟧ σ S (T , diff , tm) = [ σ ]`⊗ T , S `⊗ʳ diff , tm

        ⟦⊗[]⟧ : ∀ {σ k} τ {S₁ S₂ : Cover σ} →
               Σ[ S ∈ Cover σ ] S₂ ≡ S₁ ─ S × ｢ S ｣ ⊢ `κ k →
               Σ[ ST ∈ Cover $ σ `⊗ τ ] S₂ `⊗[ τ ] ≡ S₁ `⊗[ τ ] ─ ST × ｢ ST ｣ ⊢ `κ k
        ⟦⊗[]⟧ τ (S , diff , tm) = S `⊗[ τ ] , diff `⊗[ τ ] , tm

        ⟦[]⊗⟧ : ∀ σ {τ k} {T₁ T₂ : Cover τ} →
               Σ[ T ∈ Cover τ ] T₂ ≡ T₁ ─ T × ｢ T ｣ ⊢ `κ k →
               Σ[ ST ∈ Cover $ σ `⊗ τ ] [ σ ]`⊗ T₂ ≡ [ σ ]`⊗ T₁ ─ ST × ｢ ST ｣ ⊢ `κ k
        ⟦[]⊗⟧ σ (T , diff , tm) = [ σ ]`⊗ T , [ σ ]`⊗ diff , tm

        ⟦&ˡ⟧ : ∀ {σ} {S₁ S₂ : Cover σ} τ {k} →
              Σ[ S ∈ Cover σ ] S₂ ≡ S₁ ─ S × ｢ S ｣ ⊢ `κ k →
              Σ[ ST ∈ Cover $ σ `& τ ] S₂ `&[ τ ] ≡ S₁ `&[ τ ] ─ ST × ｢ ST ｣ ⊢ `κ k
        ⟦&ˡ⟧ τ {k} (S , diff , tm) = S `&[ τ ] , diff `&[ τ ] , tm
 
        ⟦&ʳ⟧ : ∀ σ {τ} {T₁ T₂ : Cover τ} {k} →
              Σ[ T ∈ Cover τ ] T₂ ≡ T₁ ─ T × ｢ T ｣ ⊢ `κ k →
              Σ[ ST ∈ Cover $ σ `& τ ] [ σ ]`& T₂ ≡ [ σ ]`& T₁ ─ ST × ｢ ST ｣ ⊢ `κ k
        ⟦&ʳ⟧ σ (T , diff , tm) = [ σ ]`& T , [ σ ]`& diff , tm

        ⟦_⟧ : {σ : ty} {S : Cover σ} {k : Pr} {T : Cover σ} (pr : S ∋ k ∈ T) →
              Σ[ E ∈ Cover σ ] T ≡ S ─ E × ｢ E ｣ ⊢ `κ k
        ⟦ pr `⊗ˡ T     ⟧ = ⟦⊗ˡ⟧ _ _ ⟦ pr ⟧
        ⟦ S `⊗ʳ pr     ⟧ = ⟦⊗ʳ⟧ _ _ ⟦ pr ⟧
        ⟦ [ σ ]`⊗ pr   ⟧ = ⟦[]⊗⟧ _ ⟦ pr ⟧
        ⟦ S `⊗ʳ[ prT ] ⟧ = [ _ ]`⊗ _ , S `⊗ʳ[ _ ] , FromFree.⟦ prT ⟧
        ⟦ [ prS ]`⊗ˡ T ⟧ = _ `⊗[ _ ] , [ _ ]`⊗ˡ T , FromFree.⟦ prS ⟧
        ⟦ pr `⊗[ τ ]   ⟧ = ⟦⊗[]⟧ _ ⟦ pr ⟧
        ⟦ pr `&ˡ τ     ⟧ = ⟦&ˡ⟧ _ ⟦ pr ⟧
        ⟦ σ `&ʳ pr     ⟧ = ⟦&ʳ⟧ _ ⟦ pr ⟧

    module Usage where

      open Cover
      open Linearity.Type Pr

      infix 4 _∈_▸_
      data _∈_▸_ (k : Pr) : {σ : ty} (S : Usage σ) (T : Usage σ) → Set where
        [_] : {σ : ty} {S : Cover σ} (prS : FromFree.[ σ ]∋ k ∈ S) →
              k ∈ [ σ ] ▸ ] S [
        ]_[ : {σ : ty} {S S′ : Cover σ} (prS : S FromDented.∋ k ∈ S′) →
              k ∈ ] S [ ▸ ] S′ [

      infix 4 _∋_∈_
      _∋_∈_ : {σ : ty} (S : Usage σ) (k : Pr) (T : Usage σ) → Set
      σ ∋ k ∈ τ = k ∈ σ ▸ τ

      open Context

      [∈] : ∀ {k σ} → Σ[ S ∈ Cover σ ] FromFree.[ σ ]∋ k ∈ S →
            Σ[ S ∈ Usage σ ] [ σ ] ∋ k ∈ S
      [∈] (S , prS) = ] S [ , [ prS ]

      ]∈[ : ∀ {k σ} {S : Cover σ} → Σ[ S′ ∈ Cover σ ] S FromDented.∋ k ∈ S′ →
            Σ[ S′ ∈ Usage σ ] ] S [ ∋ k ∈ S′
      ]∈[ (S , prS) = ] S [ , ] prS [

      infix 6 _∈?_
      _∈?_ : (k : Pr) {σ : ty} (S : Usage σ) → Con (Σ[ S′ ∈ Usage σ ] S ∋ k ∈ S′)
      k ∈? [ σ ] = map [∈] $ k FromFree.∈?[ σ ]
      k ∈? ] S [ = map ]∈[ $ k FromDented.∈? S

      ∈?-complete : (k : Pr) {σ : ty} (S : Usage σ) {T : Usage σ} (pr : S ∋ k ∈ T) →
                    (T , pr) BT.∈ k ∈? S
      ∈?-complete k [ σ ] [ pr ] = BTT.map [∈] (FromFree.∈?[]-complete k σ pr)
      ∈?-complete k ] S [ ] pr [ = BTT.map ]∈[ (FromDented.∈?-complete k S pr)

      module Soundness where

        open IMLL Pr
        open Consumption Pr
        open LCT.Usage
        open Linearity.Type.Cover Pr
        open Linearity.Type.Usage Pr
  
        ⟦][⟧ : {σ : ty} {S : Cover σ} {k : Pr} {T : Cover σ} →
               Σ[ E ∈ Cover σ ] T LCT.Cover.≡ S ─ E × Cover.｢ E ｣ ⊢ `κ k →
               Σ[ E ∈ Usage σ ] ] T [ ≡ ] S [ ─ E × Usage.｢ E ｣ ⊢ `κ k
        ⟦][⟧ (E , diff , tm) = ] E [ , ] diff [ , tm

        ⟦_⟧ : {σ : ty} {S : Usage σ} {k : Pr} {T : Usage σ} (pr : S ∋ k ∈ T) →
              Σ[ E ∈ Usage σ ] T ≡ S ─ E × Usage.｢ E ｣ ⊢ `κ k
        ⟦ [ prS ] ⟧ = _ , inj[ _ ] , FromFree.⟦ prS ⟧
        ⟦ ] prS [ ⟧ = ⟦][⟧ FromDented.⟦ prS ⟧

  module Context where

    module SBT = Type
    open IMLL.Type Pr
    open Con.Context
    open Linearity Pr
    open Linearity.Context Pr
    open Pointwise
    open Con.Context.Context

    infix 4 _∈_▸_ 
    data _∈_▸_ (k : Pr) : {γ : Con ty} (Γ Δ : Usage γ) → Set where
      zro : ∀ {γ σ} {Γ : Usage γ} {S S′ : LT.Usage σ} →
            S Type.Usage.∋ k ∈ S′ → k ∈ Γ ∙ S ▸ Γ ∙ S′
      suc : ∀ {γ τ} {Γ Γ′ : Usage γ} {T : LT.Usage τ} →
            k ∈ Γ ▸ Γ′ → k ∈ Γ ∙ T ▸ Γ′ ∙ T

    infix 4 _∋_∈_ 
    _∋_∈_ : {γ : Con ty} (Γ : Usage γ) (k : Pr) (Δ : Usage γ) → Set
    Γ ∋ k ∈ Δ = k ∈ Γ ▸ Δ

    ∈zro : ∀ {γ σ} (Γ : Usage γ) {S : LT.Usage σ} {k} →
           Σ[ S′ ∈ LT.Usage σ ] S Type.Usage.∋ k ∈ S′ →
           Σ[ Γ′ ∈ Usage $ γ ∙ σ ] Γ ∙ S ∋ k ∈ Γ′
    ∈zro Γ (S , prS) = Γ ∙ S , zro prS

    ∈suc : ∀ {γ σ} {Γ : Usage γ} (S : LT.Usage σ) {k} →
           Σ[ Γ′ ∈ Usage γ ] Γ ∋ k ∈ Γ′ →
           Σ[ Γ′ ∈ Usage $ γ ∙ σ ] Γ ∙ S ∋ k ∈ Γ′
    ∈suc S (Γ′ , prΓ) = Γ′ ∙ S , suc prΓ


    _∈?_ : (k : Pr) {γ : Con ty} (Γ : Usage γ) → Con (Σ[ Γ′ ∈ Usage γ ] Γ ∋ k ∈ Γ′)
    k ∈? ε       = ε
    k ∈? (Γ ∙ S) = map (∈suc S) (k ∈? Γ) ++ map (∈zro Γ) (k Type.Usage.∈? S)
      where open Con.Context.Context

    ∈?-complete : (k : Pr) {γ : Con ty} (Γ : Usage γ) {Δ : Usage γ} (pr : Γ ∋ k ∈ Δ) →
                  (Δ , pr) BT.∈ k ∈? Γ
    ∈?-complete k ε       ()
    ∈?-complete k (Γ ∙ S) (zro pr) = BTT.∈++ʳ (BTT.map (∈zro Γ) (Type.Usage.∈?-complete k S pr))
    ∈?-complete k (Γ ∙ S) (suc pr) = BTT.∈++ˡ (map (∈zro Γ) (k Type.Usage.∈? S)) 
                                              (BTT.map (∈suc S) (∈?-complete k Γ pr))

    module Soundness where

      open IMLL Pr
      open Consumption Pr
      open Consumption.Context Pr

      ⟦zro⟧ : (γ : Con ty) (Γ : Usage γ) {σ : ty} {S S′ : LT.Usage σ} (k : Pr) →
              Σ[ T ∈ LT.Usage σ ] S′ LCT.Usage.≡ S ─ T × LTU.｢ T ｣ ⊢ `κ k →
              Σ[ E ∈ Usage $ γ ∙ σ ] Γ ∙ S′ ≡ Γ ∙ S ─ E × ｢ E ｣ ⊢ `κ k
      ⟦zro⟧ γ Γ k (T , diff , tm) =
        let eq = Eq.trans (Eq.cong (flip _++_ LTU.｢ T ｣) ｢inj[ γ ]｣) $ ε++ LTU.｢ T ｣
        in LC.inj[ γ ] ∙ T
         , LCC.inj[ Γ ] ∙ diff
         , Eq.subst (flip _⊢_ (`κ k)) (Eq.sym eq) tm

      ⟦suc⟧ : {γ : Con ty} {Γ Δ : Usage γ} (σ : ty) {S : LT.Usage σ} {k : Pr} →
              Σ[ E ∈ Usage γ ] Δ ≡ Γ ─ E × ｢ E ｣ ⊢ `κ k →
              Σ[ E ∈ Usage $ γ ∙ σ ] Δ ∙ S ≡ Γ ∙ S ─ E × ｢ E ｣ ⊢ `κ k
      ⟦suc⟧ σ (E , diff , tm) = E ∙ LT.[ σ ] , diff ∙ LCT.Usage.`idˡ , tm

      ⟦_⟧ : {γ : Con ty} {Γ : Usage γ} {k : Pr} {Δ : Usage γ} (pr : Γ ∋ k ∈ Δ) →
            Σ[ E ∈ Usage γ ] Δ ≡ Γ ─ E × ｢ E ｣ ⊢ `κ k
      ⟦ zro x  ⟧ = ⟦zro⟧ _ _ _ SBT.Usage.Soundness.⟦ x ⟧
      ⟦ suc pr ⟧ = ⟦suc⟧ _ ⟦ pr ⟧