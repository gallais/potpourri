module tt.typ.prp where


open import Data.Nat
open import Data.Fin hiding (_<_)
open import Function
open import Relation.Binary.PropositionalEquality as PEq using (_≡_ ; subst ; cong)

open import tt.raw
open import tt.env
open import tt.sem
open import tt.sem.rel
open import tt.sem.fus
open import tt.typ

weakβT : {m n : ℕ} (t : Type (suc m)) (u : Infer m) (m⊆n : m ⊆ n) →
         Substitution ⊨ weakT (pop! m⊆n) t ⟨ weakI m⊆n u /0⟩T
         ≡ weakT m⊆n (Substitution ⊨ t ⟨ u /0⟩T)
weakβT {m} {n} t u m⊆n = PEq.trans eq₁ $ PEq.sym eq₂ where

  boringDiag : {m : ℕ} → ∀[ _≡_ ] (Semantics.diag Substitution {m}) (pack `var)
  boringDiag zero    = PEq.refl
  boringDiag (suc k) = cong (weakI extend) (boringDiag k)

  eq₁ : Substitution ⊨ weakT (pop! m⊆n) t ⟨ weakI m⊆n u /0⟩T
      ≡ Substitution ⊨⟦ t ⟧T (trans m⊆n (pack `var) ∙ weakI m⊆n u)
  eq₁ = fusion.lemmaT RenSub t (λ { zero → PEq.refl ; (suc k) → boringDiag {n} (lookup m⊆n k) })

  eq₂ : weakT m⊆n (Substitution ⊨ t ⟨ u /0⟩T)
      ≡ Substitution ⊨⟦ t ⟧T (trans m⊆n (pack `var) ∙ weakI m⊆n u)
  eq₂ = fusion.lemmaT SubRen t (λ { zero → PEq.refl ; (suc k) → cong (weakI m⊆n) (boringDiag k) })

module TypingWeak
       (_↝_ : {n : ℕ} (a b : Type n) → Set)
       (weak↝ : {m n : ℕ} {a b : Type m} (inc : m ⊆ n) → a ↝ b → weakT inc a ↝ weakT inc b)
       where

  open Typing _↝_

  mutual

    weak∈ : {m n : ℕ} {Γ : Context m} {Δ : Context n} {i : Infer m} {A : Type m}
            (m⊆n : m ⊆ n) (ren : [ m⊆n ] Γ ⇒ Δ) (t : Γ ⊢ i ∈ A) → Δ ⊢ weakI m⊆n i ∈ weakT m⊆n A
    weak∈ m⊆n ren (`var v)       = `var (weakVar ren v)
    weak∈ m⊆n ren (`ann t)       = `ann (weak∋ m⊆n ren t)
    weak∈ m⊆n ren (`fst t)       = `fst (weak∈ m⊆n ren t)
    weak∈ m⊆n ren (`ind p z s m) = {!!}
    weak∈ m⊆n ren (`red red t)   = `red (weak↝ m⊆n red) (weak∈ m⊆n ren t)
    weak∈ m⊆n ren (`snd {t} {A} {B} Ht)       =
      let ih  : _ ⊢ weakI m⊆n (`snd t) ∈ (Substitution ⊨ weakT _ B ⟨ weakI m⊆n (`fst t) /0⟩T)
          ih  = `snd (weak∈ m⊆n ren Ht)
      in subst (_ ⊢ weakI m⊆n (`snd t) ∈_) (weakβT B (`fst t) m⊆n) ih

    weak∈ m⊆n ren (`app {f} {t} {A} {B} Hf Ht) =
      let ih  : _ ⊢ weakI m⊆n (`app f t) ∈ Substitution ⊨ weakT _ B ⟨ weakI m⊆n (`ann t A) /0⟩T
          ih  = `app (weak∈ m⊆n ren Hf) (weak∋ m⊆n ren Ht)
          
      in subst (_ ⊢ weakI m⊆n (`app f t) ∈_) (weakβT B (`ann t A) m⊆n) ih


    weak∋ : {m n : ℕ} {Γ : Context m} {Δ : Context n} {c : Check m} {A : Type m}
            (m⊆n : m ⊆ n) (ren : [ m⊆n ] Γ ⇒ Δ) → Γ ⊢ A ∋ c → Δ ⊢ weakT m⊆n A ∋ weakC m⊆n c
    weak∋ m⊆n ren (`lam b)     = `lam (weak∋ (pop! m⊆n) {!!} b)
    weak∋ m⊆n ren (`per {a} {b} {A} {B} Ha Hb)   =
      let ih  : _ ⊢ weakT m⊆n (Substitution ⊨ B ⟨ `ann a A /0⟩T) ∋ weakC m⊆n b
          ih  = weak∋ m⊆n ren Hb

      in `per (weak∋ m⊆n ren Ha) (subst (_ ⊢_∋ weakC m⊆n b) (PEq.sym $ weakβT B (`ann a A) m⊆n) ih)

    weak∋ m⊆n ren `zro         = `zro
    weak∋ m⊆n ren (`suc m)     = `suc (weak∋ m⊆n ren m)
    weak∋ m⊆n ren (`emb e)     = `emb (weak∈ m⊆n ren e)
    weak∋ m⊆n ren (`red red t) = `red (weak↝ m⊆n red) (weak∋ m⊆n ren t)

{-
infixr 0 _$′_
_$′_ : {A B : Set} → (A → B) → A → B
_$′_ = _$_

var : (m : ℕ) {n : ℕ} (k : Fin n) → Infer (m ℕ.+ n)
var m k = `var (raise m k)

var′ : (m : ℕ) {n : ℕ} (k : Fin n) → Check (m ℕ.+ n)
var′ m k = `emb (var m k)

lam : {n : ℕ} (t : Fin (suc n) → Check (suc n)) → Check n
lam t = `lam $ t zero

add : Check 0
add = lam $′ λ m →
      lam $′ λ n → `emb $′
      `ind (`lam `nat) (var′ 0 n) (`lam $′ lam $′ `suc ∘′ var′ 0) (var 1 m)

TypeCheckAdd : ⟨⟩ ⊢ `nat `→ `nat `→ `nat ∋ add
TypeCheckAdd =
  `lam $′
  `lam $′ `emb $′ `red prf $′
  `ind TypeCheckP TypeCheckVarN TypeCheckS $′ `var (suc zero)

  where

    p   = `lam `nat
    pTy : {n : ℕ} → Check n
    pTy = `pi `nat (`set 0)

    P : {m : ℕ} → 2 ⊆ m → Check m → Check m
    P = λ inc x → `emb (`app (`ann (weakC inc p) pTy) x)

    n   = var′ 0 zero
    nTy = P refl `zro

    TypeCheckVarN : _ ⊢ nTy ∋ n
    TypeCheckVarN = `red prf $′ `emb $′ `var zero
      where
        prf : nTy ↝ `nat
        prf = admit

    TypeCheckP : _ ⊢ pTy ∋ p
    TypeCheckP = `lam `nat

    s   = `lam $′ lam $′ `suc ∘′ var′ 0
    sTy = `pi `nat (P extend var₀ `→ P extend (`suc var₀))

    TypeCheckS : _ ⊢ sTy ∋ s
    TypeCheckS = `red prf $′ `lam $′ `lam $′ `suc $′ `emb $′ `var zero
      where
        prf : sTy ↝ `pi `nat (`nat `→ `nat)
        prf = admit
        

    prf : let P = `ann p pTy
              m = var′ 1 zero
          in `emb (`app P m) ↝ `nat
    prf = admit
-}
