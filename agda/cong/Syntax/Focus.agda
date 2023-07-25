module Syntax.Focus where

open import Agda.Primitive using (Setω)

open import Data.Bool.Base using (if_then_else_)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Nat.Base
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (⊤)

open import Function.Base using (id; _$_; case_of_)

open import Reflection
import Reflection.AST.Name as Name
open import Reflection.AST.DeBruijn using (weaken; weakenArgs)
open import Reflection.TCM

open import Relation.Nullary.Decidable.Core using (does)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym; module ≡-Reasoning)

abstract

  ⟪_⟫ : ∀ {a} {A : Set a} → A → A
  ⟪ x ⟫ = x

  hole-identity : ∀ {a} {A : Set a} (x : A) → ⟪ x ⟫ ≡ x
  hole-identity x = refl

nameOf : ∀ {a} {A : Set a} → A → TC Name
nameOf x
  = do def f _ ← quoteTC x
         where _ → typeError (strErr "Not a definition" ∷ [])
       pure f

Focus : ∀ {a} (A : Set a) → Set a
Focus A = Term × (Term → A)

focus : Name → Term → TC (Maybe (Focus Term))

focusArgs : Name → List (Arg Term) → TC (Maybe (Focus (List (Arg Term))))
focusArgs nm [] = pure nothing
focusArgs nm (arg i t ∷ as)
  = do nothing ← focus nm t
         where just (foc , ctx) → pure (just (foc , λ x → arg i (ctx x) ∷ weakenArgs 1 as))
       nothing ← focusArgs nm as
         where just (foc , ctx) → pure (just (foc , λ x → arg i (weaken 1 t) ∷ ctx x))
       pure nothing
focus foc (def f args@(_ ∷ _ ∷ arg _ t ∷ _)) =
  if does (foc Name.≟ f) then pure (just (t , id)) else
    do just (foc , ctx) ← focusArgs foc args
         where nothing → pure nothing
       pure (just (foc , λ x → def f (ctx x)))
focus foc (def f args)
  = do just (foc , ctx) ← focusArgs foc args
         where nothing → pure nothing
       pure (just (foc , λ x → def f (ctx x)))
focus foc (var f args)
  = do just (foc , ctx) ← focusArgs foc args
         where nothing → pure nothing
       pure (just (foc , λ x → var (suc f) (ctx x)))
focus foc (con c args)
  = do just (foc , ctx) ← focusArgs foc args
         where nothing → pure nothing
       pure (just (foc , λ x → con c (ctx x)))
focus foc t = pure nothing

mkArg : _ → Term → Arg Term
mkArg vis = arg (arg-info vis (modality relevant quantity-ω))

congruence : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) →
             ∀ {x y} → x ≡ y → f ⟪ x ⟫ ≡ f y
congruence f eq = trans (cong f (hole-identity _)) (cong f eq)

`cong : ∀ {a} {A : Set a} {x y : A} → Focus Term → x ≡ y → TC Term
`cong (foc , ctx) x≡y
  = do `congruence ← nameOf (congruence id x≡y)
       `x≡y ← quoteTC x≡y
       let hmm = mkArg hidden unknown
       pure $ def `congruence
            $ hmm ∷ hmm ∷ hmm ∷ hmm
            ∷ mkArg visible (lam visible (abs "focus" (ctx (var 0 [])))) ∷ hmm ∷ hmm
            ∷ mkArg visible `x≡y ∷ []

`trans : Term → Term → TC Term
`trans x≡y y≡z
  = do `transitivity ← nameOf (trans (refl {x = 0}) (refl {x = 0}))
       let hmm = mkArg hidden unknown
       pure $ def `transitivity
            $ hmm ∷ hmm ∷ hmm ∷ hmm ∷ hmm
            ∷ mkArg visible x≡y
            ∷ mkArg visible y≡z
            ∷ []

`sym : Term → TC Term
`sym x≡y
  = do `symmetry ← nameOf (sym (refl {x = 0}))
       let hmm = mkArg hidden unknown
       pure $ def `symmetry
            $ hmm ∷ hmm ∷ hmm ∷ hmm
            ∷ mkArg visible x≡y
            ∷ []

{-# TERMINATING #-}
congr : ∀ {a} {A : Set a} {x y : A} → x ≡ y → Term → TC ⊤
congr {y = y} x≡y goal
    = do (def _ (_ ∷ _ ∷ arg _ lhs ∷ arg _ rhs ∷ [])) ← inferType goal
           where
             (meta m args) → do blockOnMeta {A = ⊤} m
                                congr x≡y goal
             _ → typeError (strErr "Oops, wrong goal" ∷ [])
         foc ← nameOf ⟪ 0 ⟫
         just ctx ← focus foc lhs
           where nothing → {!!}

         mctx′ ← focus foc rhs
         proof ← case mctx′ of λ where
           nothing → `cong ctx x≡y
           (just ctx′) → do fst ← `cong ctx x≡y
                            snd ← `cong ctx′ (refl {x = y})
                            dns ← `sym snd
                            `trans fst dns

         unify goal proof


{-# TERMINATING #-}
beginr : ∀ {a} {A : Set a} {x y : A} → x ≡ y → Term → TC ⊤
beginr {x = x} x≡y goal
    = do lhs ← quoteTC x
         prf ← quoteTC x≡y
         foc ← nameOf ⟪ 0 ⟫
         just ctx@(t , _) ← focus foc lhs
           where nothing → unify goal prf

         fst ← `cong ctx (refl {x = t})
         tsf ← `sym fst
         prf ← `trans tsf prf
         unify goal prf

infix  1 beginn_

macro
  congg = congr
  beginn_ = beginr



open import Data.Nat.Properties

open ≡-Reasoning

test : (m n p : ℕ) →
       (m + n) + (n + p) ≡ (n + m) + (p + n)
test m n p = beginn
  m + n + ⟪ n + p ⟫   ≡⟨ congg (+-comm n p) ⟩
  ⟪ m + n ⟫ + (p + n) ≡⟨ congg (+-comm m n) ⟩
  n + m + (p + n)     ∎
