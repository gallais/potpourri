import lps.IMLL         as IMLL
import lps.Linearity    as Linearity

open import Data.Product hiding (map)
open import Data.Nat
open import Function

import lib.Context as Con
open import lib.Maybe
open import lib.Nullary

open import Relation.Nullary

module lps.Linearity.Action where

  module Type where
 
    open IMLL.Type

    module Cover where

      open Linearity.Type
      open Linearity.Type.Cover

      -- this action is a notion of synchronization. It imposes restrictions
      -- on the sort of output contexts we can consider identical (see the
      -- right rule for `& to have a feeling of why we need this sort of
      -- thing)
      infix 4 _≡_⊙_
      data _≡_⊙_ : {σ : ty} (S S₁ S₂ : Cover σ) → Set where
        sym      : {a : ty} {A B C : Cover a} (pr : A ≡ B ⊙ C) → A ≡ C ⊙ B
        `κ       : (k : ℕ) → `κ k ≡ `κ k ⊙ `κ k
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

    module Usage where

      open Linearity.Type
      open Linearity.Type.Usage

      infix 4 _≡_⊙_
      data _≡_⊙_ : {σ : ty} (S S₁ S₂ : Usage σ) → Set where
        [_] : (σ : ty) → [ σ ] ≡ [ σ ] ⊙ [ σ ]
        ]_[ : {σ : ty} {A A₁ A₂ : Cover σ} (prA : A Cover.≡ A₁ ⊙ A₂) →
              ] A [ ≡ ] A₁ [ ⊙ ] A₂ [
 
      open Maybe
      infix 3 _⊙?_
      _⊙?_ : {a : ty} (A B : Usage a) → Maybe (Σ[ C ∈ Usage a ] C ≡ A ⊙ B)
      [ a ] ⊙? [ .a ] = return $ [ a ] , [ a ]
      ] A [ ⊙? ] B [  = A Cover.⊙? B >>= uncurry $ λ C prC →
                        return $ ] C [ , ] prC [
      _ ⊙? _ = none

  module Context where

    open IMLL.Type
    open Linearity
    open Linearity.Context
    open Con.Context
    open Pointwise

    infix 4 _≡_⊙_
    data _≡_⊙_ : {γ : Con ty} (E Δ₁ Δ₂ : Usage γ) → Set where
      ε   : ε ≡ ε ⊙ ε
      _∙_ : ∀ {γ σ} {Γ Δ₁ Δ₂ : Usage γ} {S S₁ S₂ : Type.Usage σ} →
            (prΓ : Γ ≡ Δ₁ ⊙ Δ₂) (prS : S Type.Usage.≡ S₁ ⊙ S₂) →
            Γ ∙ S ≡ Δ₁ ∙ S₁ ⊙ Δ₂ ∙ S₂

    open Maybe
    infix 5 _⊙?_
    _⊙?_ : {γ : Con ty} (Δ₁ Δ₂ : Usage γ) → Maybe (Σ[ E ∈ Usage γ ] E ≡ Δ₁ ⊙ Δ₂)
    ε       ⊙? ε       = return $ ε , ε
    Δ₁ ∙ S₁ ⊙? Δ₂ ∙ S₂ =
      Δ₁ ⊙? Δ₂            >>= uncurry $ λ E prE →
      S₁ Type.Usage.⊙? S₂ >>= uncurry $ λ S prS →
      return $ E ∙ S , prE ∙ prS

module LAT = Type
module LAC = Context