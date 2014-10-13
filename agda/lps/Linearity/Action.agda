import lps.IMLL         as IMLL
import lps.Linearity    as Linearity

open import Data.Product hiding (map)
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Nat
open import Function

import lib.Context as Con
open import lib.Maybe
open import lib.Nullary

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

module lps.Linearity.Action (Pr : Set) where

  module Type where
 
    open IMLL.Type Pr

    module Cover where

      open Linearity.Type Pr
      open Linearity.Type.Cover Pr

      -- this action is a notion of synchronization. It imposes restrictions
      -- on the sort of output contexts we can consider identical (see the
      -- right rule for `& to have a feeling of why we need this sort of
      -- thing)
      infix 4 _≡_⊙_
      data _≡_⊙_ : {σ : ty} (S S₁ S₂ : Cover σ) → Set where
        sym      : {a : ty} {A B C : Cover a} (pr : A ≡ B ⊙ C) → A ≡ C ⊙ B
        `κ       : (k : Pr) → `κ k ≡ `κ k ⊙ `κ k
        _`⊗_     : {a b : ty} {A A₁ A₂ : Cover a} {B B₁ B₂ : Cover b} →
                   (prA : A ≡ A₁ ⊙ A₂) (prB : B ≡ B₁ ⊙ B₂) → 
                   A `⊗ B ≡ A₁ `⊗ B₁ ⊙ A₂ `⊗ B₂
        [_]`⊗_   : {a : ty} {A A₁ A₂ : Cover a} (prA : A ≡ A₁ ⊙ A₂) (b : ty) →
                   A `⊗[ b ] ≡ A₁ `⊗[ b ] ⊙ A₂ `⊗[ b ]
        _`⊗[_]   : (a : ty) {b : ty} {B B₁ B₂ : Cover b} (prB : B ≡ B₁ ⊙ B₂) →
                   [ a ]`⊗ B ≡ [ a ]`⊗ B₁ ⊙ [ a ]`⊗ B₂
        _`&_     : (a b : ty) → a `& b ≡ a `& b ⊙ a `& b
        ]_[`&]_[ : {a b : ty} {A : Cover a} {B : Cover b}
                   (prA : isUsed A) (prB : isUsed B) →
                    a `& b ≡ A `&[ b ] ⊙ [ a ]`& B
        ]_[`&    : {a b : ty} {B : Cover b} (prB : isUsed B) →
                   a `& b ≡ [ a ]`& B ⊙ a `& b
        `&]_[    : {a b : ty} {A : Cover a} (prA : isUsed A) →
                   a `& b ≡ A `&[ b ] ⊙ a `& b
        _`&[_]   : {a : ty} {A A₁ A₂ : Cover a} (prA : A ≡ A₁ ⊙ A₂) (b : ty) →
                   A `&[ b ] ≡ A₁ `&[ b ] ⊙ A₂ `&[ b ]
        [_]`&_   : (a : ty) {b : ty} {B B₁ B₂ : Cover b} (prB : B ≡ B₁ ⊙ B₂) →
                   [ a ]`& B ≡ [ a ]`& B₁ ⊙ [ a ]`& B₂

      ⊙-refl : {σ : ty} (S : Cover σ) → S ≡ S ⊙ S
      ⊙-refl (`κ k)      = `κ k
      ⊙-refl (S `⊗ T)    = ⊙-refl S `⊗ ⊙-refl T
      ⊙-refl ([ σ ]`⊗ T) = σ `⊗[ ⊙-refl T ]
      ⊙-refl (S `⊗[ τ ]) = [ ⊙-refl S ]`⊗ τ
      ⊙-refl (σ `& τ)    = σ `& τ
      ⊙-refl (S `&[ τ ]) = ⊙-refl S `&[ τ ]
      ⊙-refl ([ σ ]`& T) = [ σ ]`& ⊙-refl T

      open Maybe
      infix 3 _⊙?_
      _⊙?_ : {a : ty} (A B : Cover a) → Maybe (Σ[ C ∈ Cover a ] C ≡ A ⊙ B)
      `κ k      ⊙? `κ .k      = return $ `κ k , `κ k
      A₁ `⊗ A₂  ⊙? B₁ `⊗ B₂   = A₁ ⊙? B₁ >>= uncurry $ λ C₁ prC₁ →
                                A₂ ⊙? B₂ >>= uncurry $ λ C₂ prC₂ →
                                return $ C₁ `⊗ C₂ , prC₁ `⊗ prC₂
      [ a ]`⊗ A ⊙? [ .a ]`⊗ B = A ⊙? B >>= uncurry $ λ C prC →
                                return $ [ a ]`⊗ C , a `⊗[ prC ]
      A `⊗[ b ] ⊙? B `⊗[ .b ] = A ⊙? B >>= uncurry $ λ C prC →
                                return $ C `⊗[ b ] , [ prC ]`⊗ b
      a `& b    ⊙? .a `& .b   = return $ a `& b , a `& b
      a `& b    ⊙? B `&[ .b ] = flip (dec (isUsed? B)) (const none) $ λ prB →
                                return $ a `& b , sym (`&] prB [)
      a `& b    ⊙? [ .a ]`& B = flip (dec (isUsed? B)) (const none) $ λ prB →
                                return $ a `& b , sym ] prB [`&
      A `&[ b ] ⊙? a `& .b    = flip (dec (isUsed? A)) (const none) $ λ prA →
                                return $ a `& b , `&] prA [
      A `&[ b ] ⊙? B `&[ .b ] = A ⊙? B >>= uncurry $ λ C prC →
                                return $ C `&[ b ] , prC `&[ b ]
      A `&[ b ] ⊙? [ a ]`& B  = flip (dec (isUsed? A)) (const none) $ λ prA →
                                flip (dec (isUsed? B)) (const none) $ λ prB →
                                return $ a `& b , ] prA [`&] prB [
      [ a ]`& A ⊙? .a `& b    = flip (dec (isUsed? A)) (const none) $ λ prA →
                                return $ a `& b , ] prA [`&
      [ a ]`& A ⊙? B `&[ b ]  = flip (dec (isUsed? A)) (const none) $ λ prA →
                                flip (dec (isUsed? B)) (const none) $ λ prB →
                                return $ a `& b , sym (] prB [`&] prA [)
      [ a ]`& A ⊙? [ .a ]`& B = A ⊙? B >>= uncurry $ λ C prC →
                                return $ [ a ]`& C , [ a ]`& prC
      _ ⊙? _ = none

      mutual

        ⊙?-complete′ : {a : ty} (A B C : Cover a) (pr : C ≡ A ⊙ B) →
                       Σ[ pr ∈ C ≡ B ⊙ A ] (B ⊙? A) ≡ some (C , pr)
        ⊙?-complete′ B A C (sym pr) = ⊙?-complete A B C pr
        ⊙?-complete′ ._ ._ ._ (`κ k) = `κ k , Eq.refl
        ⊙?-complete′ (A₂ `⊗ B₂) (A₁ `⊗ B₁) ._ (pr₁ `⊗ pr₂)
          with A₁ ⊙? A₂ | ⊙?-complete′ A₂ A₁ _ pr₁
             | B₁ ⊙? B₂ | ⊙?-complete′ B₂ B₁ _ pr₂
        ... | ._ | C₁ , Eq.refl | ._ | C₂ , Eq.refl = C₁ `⊗ C₂ , Eq.refl
        ⊙?-complete′ (A₂ `⊗[ .b ]) (A₁ `⊗[ .b ]) ._ ([ pr ]`⊗ b)
          with A₁ ⊙? A₂ | ⊙?-complete′ A₂ A₁ _ pr
        ... | ._ | C , Eq.refl = [ C ]`⊗ b , Eq.refl
        ⊙?-complete′ ([ .a ]`⊗ B₂) ([ .a ]`⊗ B₁) ._ (a `⊗[ pr ])
          with B₁ ⊙? B₂ | ⊙?-complete′ B₂ B₁ _ pr
        ... | ._ | C , Eq.refl = a `⊗[ C ] , Eq.refl
        ⊙?-complete′ ._ ._ ._ (a `& b) = a `& b , Eq.refl
        ⊙?-complete′ (A `&[ b ]) ([ a ]`& B) ._ ] prA [`&] prB [ with isUsed? A | isUsed? B
        ... | yes p₁ | yes p₂ = sym ] p₁ [`&] p₂ [ , Eq.refl
        ... | no ¬p₁ | _      = ⊥-elim $ ¬p₁ prA
        ... | _      | no ¬p₂ = ⊥-elim $ ¬p₂ prB
        ⊙?-complete′ ([ a ]`& B) ._ ._ ] prB [`& with isUsed? B
        ... | yes p = sym ] p [`& , Eq.refl
        ... | no ¬p = ⊥-elim $ ¬p prB
        ⊙?-complete′ (A `&[ b ]) ._ ._ `&] prA [ with isUsed? A
        ... | yes p = sym `&] p [ , Eq.refl
        ... | no ¬p = ⊥-elim $ ¬p prA
        ⊙?-complete′ (A₂ `&[ .b ]) (A₁ `&[ .b ]) ._ (pr `&[ b ])
          with A₁ ⊙? A₂ | ⊙?-complete′ A₂ A₁ _ pr
        ... | ._ | C , Eq.refl = C `&[ b ] , Eq.refl
        ⊙?-complete′ ([ .a ]`& B₂) ([ .a ]`& B₁) ._ ([ a ]`& pr)
          with B₁ ⊙? B₂ | ⊙?-complete′ B₂ B₁ _ pr
        ... | ._ | C , Eq.refl = [ a ]`& C , Eq.refl

        ⊙?-complete : {a : ty} (A B C : Cover a) (pr : C ≡ A ⊙ B) →
                    Σ[ pr ∈ C ≡ A ⊙ B ] (A ⊙? B) ≡ some (C , pr)
        ⊙?-complete A B C (sym pr) = ⊙?-complete′ B A C pr
        ⊙?-complete ._ ._ ._ (`κ k) = `κ k , Eq.refl
        ⊙?-complete (A₁ `⊗ B₁) (A₂ `⊗ B₂) ._ (pr₁ `⊗ pr₂)
          with A₁ ⊙? A₂ | ⊙?-complete A₁ A₂ _ pr₁
             | B₁ ⊙? B₂ | ⊙?-complete B₁ B₂ _ pr₂
        ... | ._ | C₁ , Eq.refl | ._ | C₂ , Eq.refl = C₁ `⊗ C₂ , Eq.refl
        ⊙?-complete (A₁ `⊗[ .b ]) (A₂ `⊗[ .b ]) ._ ([ pr ]`⊗ b)
          with A₁ ⊙? A₂ | ⊙?-complete A₁ A₂ _ pr
        ... | ._ | C , Eq.refl = [ C ]`⊗ b , Eq.refl
        ⊙?-complete ([ .a ]`⊗ B₁) ([ .a ]`⊗ B₂) ._ (a `⊗[ pr ])
          with B₁ ⊙? B₂ | ⊙?-complete B₁ B₂ _ pr
        ... | ._ | C , Eq.refl = a `⊗[ C ] , Eq.refl
        ⊙?-complete ._ ._ ._ (a `& b) = a `& b , Eq.refl
        ⊙?-complete (A `&[ b ]) ([ a ]`& B) ._ ] prA [`&] prB [ with isUsed? A | isUsed? B
        ... | yes p₁ | yes p₂ = ] p₁ [`&] p₂ [ , Eq.refl
        ... | no ¬p₁ | _      = ⊥-elim $ ¬p₁ prA
        ... | _      | no ¬p₂ = ⊥-elim $ ¬p₂ prB
        ⊙?-complete ([ a ]`& B) ._ ._ ] prB [`& with isUsed? B
        ... | yes p = ] p [`& , Eq.refl
        ... | no ¬p = ⊥-elim $ ¬p prB
        ⊙?-complete (A `&[ b ]) ._ ._ `&] prA [ with isUsed? A
        ... | yes p = `&] p [ , Eq.refl
        ... | no ¬p = ⊥-elim $ ¬p prA
        ⊙?-complete (A₁ `&[ .b ]) (A₂ `&[ .b ]) ._ (pr `&[ b ])
          with A₁ ⊙? A₂ | ⊙?-complete A₁ A₂ _ pr
        ... | ._ | C , Eq.refl = C `&[ b ] , Eq.refl
        ⊙?-complete ([ .a ]`& B₁) ([ .a ]`& B₂) ._ ([ a ]`& pr)
          with B₁ ⊙? B₂ | ⊙?-complete B₁ B₂ _ pr
        ... | ._ | C , Eq.refl = [ a ]`& C , Eq.refl

    module Usage where

      open Linearity.Type Pr
      open Linearity.Type.Usage Pr

      infix 4 _≡_⊙_
      data _≡_⊙_ : {σ : ty} (S S₁ S₂ : Usage σ) → Set where
        [_] : (σ : ty) → [ σ ] ≡ [ σ ] ⊙ [ σ ]
        ]_[ : {σ : ty} {A A₁ A₂ : Cover σ} (prA : A Cover.≡ A₁ ⊙ A₂) →
              ] A [ ≡ ] A₁ [ ⊙ ] A₂ [
 
      ⊙-refl : {σ : ty} (S : Usage σ) → S ≡ S ⊙ S
      ⊙-refl [ σ ] = [ σ ]
      ⊙-refl ] S [ = ] Cover.⊙-refl S [

      open Maybe
      infix 3 _⊙?_
      _⊙?_ : {a : ty} (A B : Usage a) → Maybe (Σ[ C ∈ Usage a ] C ≡ A ⊙ B)
      [ a ] ⊙? [ .a ] = return $ [ a ] , [ a ]
      ] A [ ⊙? ] B [  = A Cover.⊙? B >>= uncurry $ λ C prC →
                        return $ ] C [ , ] prC [
      _ ⊙? _ = none

      ⊙?-complete : {a : ty} (A B : Usage a) {C : Usage a} (pr : C ≡ A ⊙ B) →
                    Σ[ pr ∈ C ≡ A ⊙ B ] (A ⊙? B) ≡ some (C , pr)
      ⊙?-complete [ a ] [ .a ] [ .a ] = [ a ] , Eq.refl
      ⊙?-complete ] A [ ] B [  ] pr [ with A Cover.⊙? B | Cover.⊙?-complete A B _ pr
      ... | ._ | C , Eq.refl = ] C [ , Eq.refl


  module Context where

    open IMLL.Type Pr
    open Linearity Pr
    open Linearity.Context Pr
    open Con.Context
    open Pointwise

    infix 4 _≡_⊙_
    data _≡_⊙_ : {γ : Con ty} (E Δ₁ Δ₂ : Usage γ) → Set where
      ε   : ε ≡ ε ⊙ ε
      _∙_ : ∀ {γ σ} {Γ Δ₁ Δ₂ : Usage γ} {S S₁ S₂ : Type.Usage σ} →
            (prΓ : Γ ≡ Δ₁ ⊙ Δ₂) (prS : S Type.Usage.≡ S₁ ⊙ S₂) →
            Γ ∙ S ≡ Δ₁ ∙ S₁ ⊙ Δ₂ ∙ S₂

    ⊙-refl : {γ : Con ty} (Γ : Usage γ) → Γ ≡ Γ ⊙ Γ
    ⊙-refl ε       = ε
    ⊙-refl (Γ ∙ S) = ⊙-refl Γ ∙ Type.Usage.⊙-refl S

    open Maybe
    infix 5 _⊙?_
    _⊙?_ : {γ : Con ty} (Δ₁ Δ₂ : Usage γ) → Maybe (Σ[ E ∈ Usage γ ] E ≡ Δ₁ ⊙ Δ₂)
    ε       ⊙? ε       = return $ ε , ε
    Δ₁ ∙ S₁ ⊙? Δ₂ ∙ S₂ =
      Δ₁ ⊙? Δ₂            >>= uncurry $ λ E prE →
      S₁ Type.Usage.⊙? S₂ >>= uncurry $ λ S prS →
      return $ E ∙ S , prE ∙ prS

    ⊙?-complete : {γ : Con ty} (Δ₁ Δ₂ : Usage γ) {E : Usage γ} (pr : E ≡ Δ₁ ⊙ Δ₂) →
                  Σ[ pr ∈ E ≡ Δ₁ ⊙ Δ₂ ] (Δ₁ ⊙? Δ₂) ≡ some (E , pr)
    ⊙?-complete .ε .ε ε = ε , Eq.refl
    ⊙?-complete (Δ₁ ∙ S₁) (Δ₂ ∙ S₂) (prΔ ∙ prS)
         with Δ₁ ⊙? Δ₂ | ⊙?-complete Δ₁ Δ₂ prΔ
            | S₁ Type.Usage.⊙? S₂ | Type.Usage.⊙?-complete S₁ S₂ prS
    ... | ._ | E , Eq.refl | ._ | S , Eq.refl = E ∙ S , Eq.refl

module LAT = Type
module LAC = Context