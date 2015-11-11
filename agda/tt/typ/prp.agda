module tt.typ.prp where


open import Data.Nat
open import Data.Fin hiding (_<_)
open import Function

open import tt.raw
open import tt.env
open import tt.sem
open import tt.typ

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
      let ih : _ ⊢ weakI m⊆n (`snd t) ∈ (Substitution ⊨ weakT _ B ⟨ weakI m⊆n (`fst t) /0⟩T)
          ih = `snd (weak∈ m⊆n ren Ht)
      in {!!}
    weak∈ m⊆n ren (`app {f} {t} {A} {B} Hf Ht) =
      let ih : _ ⊢ weakI m⊆n (`app f t) ∈ Substitution ⊨ weakT _ B ⟨ weakI m⊆n (`ann t A) /0⟩T
          ih = `app (weak∈ m⊆n ren Hf) (weak∋ m⊆n ren Ht)
      in {!!}


    weak∋ : {m n : ℕ} {Γ : Context m} {Δ : Context n} {c : Check m} {A : Type m}
            (m⊆n : m ⊆ n) (ren : [ m⊆n ] Γ ⇒ Δ) → Γ ⊢ A ∋ c → Δ ⊢ weakT m⊆n A ∋ weakC m⊆n c
    weak∋ m⊆n ren t = {!!}


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
