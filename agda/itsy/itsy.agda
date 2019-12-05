module itsy where

open import Data.Nat.Base  using (ℕ; _+_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Vec.Base  using (Vec; []; _∷_)
open import Data.Product   using (_×_ ; _,_; ∃)
open import Relation.Binary.PropositionalEquality
  using (_≡_) renaming (refl to trivial)

infix 5 _<_>

record ITSY : Set where
  constructor _<_>
  field AC  : ℕ
        MEM : Vec ℕ 4
open ITSY

data ADDR : Set where
  `0 `1 `2 `3 : ADDR

data INSTR : Set where
  LOAD  : ADDR → INSTR
  STORE : ADDR → INSTR
  ADD   : ADDR → INSTR
  PRINT : INSTR

ASM : Set
ASM = List INSTR

sum-MEM : ASM
sum-MEM
  = LOAD `0
  ∷ ADD `1
  ∷ ADD `2
  ∷ ADD `3
  ∷ PRINT
  ∷ []

swap-03 : ASM
swap-03
  = LOAD `0
  ∷ STORE `1
  ∷ LOAD `3
  ∷ STORE `0
  ∷ LOAD `1
  ∷ STORE `3
  ∷ []

ACTION : Set
ACTION = ITSY → (ITSY × List ℕ)

_!!_ : Vec ℕ 4 → ADDR → ℕ
(v ∷ _ ∷ _ ∷ _ ∷ []) !! `0 = v
(_ ∷ v ∷ _ ∷ _ ∷ []) !! `1 = v
(_ ∷ _ ∷ v ∷ _ ∷ []) !! `2 = v
(_ ∷ _ ∷ _ ∷ v ∷ []) !! `3 = v

_[_]:=_ : Vec ℕ 4 → ADDR → ℕ → Vec ℕ 4
(a ∷ b ∷ c ∷ d ∷ []) [ `0 ]:= v = v ∷ b ∷ c ∷ d ∷ []
(a ∷ b ∷ c ∷ d ∷ []) [ `1 ]:= v = a ∷ v ∷ c ∷ d ∷ []
(a ∷ b ∷ c ∷ d ∷ []) [ `2 ]:= v = a ∷ b ∷ v ∷ d ∷ []
(a ∷ b ∷ c ∷ d ∷ []) [ `3 ]:= v = a ∷ b ∷ c ∷ v ∷ []

instr : INSTR → ACTION
instr (LOAD a)  (ac < mem >) = mem !! a        < mem            > , []
instr (STORE a) (ac < mem >) = ac              < mem [ a ]:= ac > , []
instr (ADD a)   (ac < mem >) = ac + (mem !! a) < mem            > , []
instr PRINT     (ac < mem >) = ac              < mem            > , ac ∷ []

asm : ASM → ACTION
asm []       itsy = (itsy , [])
asm (i ∷ is) itsy =
  let (itsy₁ , ns₁) = instr i itsy
      (itsy₂ , ns₂) = asm is itsy₁
  in (itsy₂ , ns₁ ++ ns₂)

theorem-sum-MEM : ∀ ac mem →
  let sum = mem !! `0 + mem !! `1 + mem !! `2 + mem !! `3 in
  asm sum-MEM (ac < mem >) ≡ (sum < mem > , sum ∷ [])
theorem-sum-MEM ac (a ∷ b ∷ c ∷ d ∷ []) = trivial

theorem-swap03 : ∀ ac mem → ∃ λ mem₂ →
    asm swap-03 (ac < mem >) ≡ ((mem !! `0) < mem₂ > , [])
  × mem₂ !! `0 ≡ mem !! `3
  × mem₂ !! `3 ≡ mem !! `0
theorem-swap03 ac (a ∷ b ∷ c ∷ d ∷ []) =
  _ , trivial , trivial , trivial

theorem-loadload : ∀ itsy l₁ l₂ is →
  asm (LOAD l₁ ∷ LOAD l₂ ∷ is) itsy ≡ asm (LOAD l₂ ∷ is) itsy
theorem-loadload (ac < a ∷ b ∷ c ∷ d ∷ [] >) l₁ l₂ is = trivial

theorem-storeload : ∀ itsy l is →
  asm (STORE l ∷ LOAD l ∷ is) itsy ≡ asm (STORE l ∷ is) itsy
theorem-storeload (ac < a ∷ b ∷ c ∷ d ∷ [] >) `0 is = trivial
theorem-storeload (ac < a ∷ b ∷ c ∷ d ∷ [] >) `1 is = trivial
theorem-storeload (ac < a ∷ b ∷ c ∷ d ∷ [] >) `2 is = trivial
theorem-storeload (ac < a ∷ b ∷ c ∷ d ∷ [] >) `3 is = trivial
