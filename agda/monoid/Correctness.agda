module monoid.Correctness where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.List
open import Algebra
open import Function
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning

open import monoid.Utils
open import monoid.Monoid
open import monoid.Normalise

_≣_ : {n : ℕ} → Expr n → Expr n → Set
e ≣ f = norm e ≡ norm f

_≈_[_,_] : {n : ℕ} → Expr n → Expr n → (c ℓ : Level) → Set _
e ≈ f [ c , ℓ ] =
  (m : Monoid c ℓ) (open Semantics m) →
  ∀ ρ → (⟦ e ⟧ ρ) Mon.≈ (⟦ f ⟧ ρ)

rawInsert-reify : {n : ℕ} {y : Fin n} (e f : Model n) →
                  rawInsert (reify e) (reify (y ∷ f)) ≡ reify (e ++ y ∷ f)
rawInsert-reify []           f = refl
rawInsert-reify (x ∷ [])     f = refl
rawInsert-reify (x ∷ y ∷ xs) f = cong (bin (var x)) (rawInsert-reify (y ∷ xs) f)

insert-reify : {n : ℕ} (e f : Model n) → insert (reify e) (reify f) ≡ reify (e ++ f)
insert-reify e []          = subst ((reify e ≡_) ∘ reify) prf refl where

  module Mon = Monoid (Data.List.monoid _) hiding (refl)

  prf : e ≡ e ++ []
  prf = Mon.sym (proj₂ Mon.identity e)

insert-reify e (y ∷ [])    = rawInsert-reify e []
insert-reify e (y ∷ z ∷ f) = rawInsert-reify e (z ∷ f)

rawInsert-sound : 
  {n : ℕ} (e f : Expr n) →
  {c ℓ : Level} (m : Monoid c ℓ) (open Semantics m) →
  ∀ ρ → ⟦ rawInsert e f ⟧ ρ Mon.≈ ⟦ e ⟧ ρ Mon.∙ ⟦ f ⟧ ρ
rawInsert-sound e f m ρ = go e f where

  open Semantics m
  open Relation.Binary.EqReasoning Mon.setoid

  go : (e f : Expr _) → ⟦ rawInsert e f ⟧ ρ Mon.≈ ⟦ e ⟧ ρ Mon.∙ ⟦ f ⟧ ρ
  go (var k)   f = Mon.refl
  go one       f = Mon.sym $ proj₁ Mon.identity $ ⟦ f ⟧ ρ
  go (bin t u) f = 
    begin
      ⟦ rawInsert (bin t u) f ⟧ ρ           ≈⟨ Mon.∙-cong Mon.refl (go u f) ⟩
      ⟦ t ⟧ ρ Mon.∙ (⟦ u ⟧ ρ Mon.∙ ⟦ f ⟧ ρ) ≈⟨ Mon.sym (Mon.assoc _ _ _) ⟩
      ⟦ bin t u ⟧ ρ Mon.∙ ⟦ f ⟧ ρ
    ∎

insert-sound :
  {n : ℕ} (e f : Expr n) →
  {c ℓ : Level} (m : Monoid c ℓ) (open Semantics m) →
  ∀ ρ → ⟦ insert e f ⟧ ρ Mon.≈ ⟦ e ⟧ ρ Mon.∙ ⟦ f ⟧ ρ
insert-sound e one       m ρ = Mon.sym (proj₂ Mon.identity (⟦ e ⟧ ρ)) where open Semantics m
insert-sound e (var k)   = rawInsert-sound e (var k)
insert-sound e (bin t u) = rawInsert-sound e (bin t u)


sound : {n : ℕ} (e f : Expr n) → e ≣ f → {c ℓ : Level} → e ≈ f [ c , ℓ ]
sound e f eq m ρ =
  begin
    ⟦ e ⟧ ρ      ≈⟨ sound-aux e ⟩
    ⟦ norm e ⟧ ρ ≈⟨ Mon.reflexive (cong (⟦_⟧ ρ) eq) ⟩ 
    ⟦ norm f ⟧ ρ ≈⟨ Mon.sym (sound-aux f) ⟩
    ⟦ f ⟧ ρ
  ∎

  where

  open Semantics m
  open Relation.Binary.EqReasoning Mon.setoid

  sound-aux : (e : Expr _) → ⟦ e ⟧ ρ Mon.≈ ⟦ norm e ⟧ ρ
  sound-aux (var k)   = Mon.refl
  sound-aux one       = Mon.refl
  sound-aux (bin e f) =
    let prf = insert-reify (eval e) (eval f) in
    begin
      ⟦ bin e f ⟧ ρ                   ≈⟨ Mon.∙-cong (sound-aux e) (sound-aux f) ⟩
      ⟦ norm e ⟧ ρ Mon.∙ ⟦ norm f ⟧ ρ ≈⟨ Mon.sym (insert-sound (norm e) (norm f) m ρ) ⟩
      ⟦ insert (norm e) (norm f) ⟧ ρ  ≈⟨ Mon.reflexive (cong (⟦_⟧ ρ) prf) ⟩
      ⟦ norm (bin e f) ⟧ ρ
    ∎

complete : {n : ℕ} (e f : Expr n) (eq : {c ℓ : Level} → e ≈ f [ c , ℓ ]) → e ≣ f
complete {n} e f eq =

  begin
    norm e           ≈⟨ Mon.sym (complete-aux e) ⟩
    ⟦ e ⟧ (pack var) ≈⟨ eq (Syntactic.monoid n) (pack var) ⟩
    ⟦ f ⟧ (pack var) ≈⟨ complete-aux f ⟩
    norm f
  ∎
    

  where
  
  open Semantics (Syntactic.monoid n)
  open Relation.Binary.EqReasoning Mon.setoid
  
  complete-aux : (e : Expr n) → ⟦ e ⟧ (pack var) ≡ norm e
  complete-aux (var k)   = refl
  complete-aux one       = refl
  complete-aux (bin e f) =
    begin
      (⟦ bin e f ⟧ pack var)   ≈⟨ cong₂ insert (complete-aux e) (complete-aux f) ⟩
      insert (norm e) (norm f) ≈⟨ insert-reify (eval e) (eval f) ⟩
      norm (bin e f)
    ∎
