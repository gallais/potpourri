{-# OPTIONS --copatterns #-}

-- The content of this file is an attempt at formalizing an
-- evaluation mechanism similar to the one described in the
-- following blog post:
-- http://siek.blogspot.co.uk/2013/05/type-safety-in-three-easy-lemmas.html

-- One of the particularities is that we work in the partiality
-- monad except that we use an applicative instance not derived
-- from the monad one. In effect, that means that we only spend
-- fuel on the recursion depth rather than on the length of the
-- evaluation (_>>=_, unlike _⊛_,  accumulates all the delays!).
-- This could be useful to implement e.g. Coq's auto in Agda in
-- terms of the delay monad rather than via the fuel-threading
-- technique used in:
-- https://github.com/pepijnkokke/AutoInAgda

module eval where

open import Level
open import Size
open import Category.Functor
open import Category.Applicative
open import Function
open import lib.Function
open import poc.delay as Delay

open import Data.Nat as Nat
open import Data.Fin as Fin
open import Data.Vec as Vec hiding (_⊛_ ; _>>=_)
open import Data.Bool
open import Data.Product
open import Relation.Nullary.Decidable

-- Little (untyped) language
data Op : Set where
  `- `+ `* `= : Op

data Term (n : ℕ) : Set where
  `Nat  : ℕ    → Term n
  `Bool : Bool → Term n
  `Op   : (l : Term n) (op : Op) (r : Term n) → Term n
  `var  : (k : Fin n) → Term n
  `ifte : (b t f : Term n) → Term n
  -- the intuition behind the recursive definition:
  -- rec f x $ t ~~~> f [rec f x / f, t / x]
  `rec  : (b : Term (2 Nat.+ n)) → Term n
  `app  : (f t : Term n) → Term n

-- Because the language is untyped, evaluation may crash:
data Result (A : Set) : Set where
  value : (a : A) → Result A
  stuck : Result A

fmap2 : {A B C : Set} (f : A → B → C) (a : Result A) (b : Result B) → Result C
fmap2 f (value a) (value b) = value $ f a b
fmap2 f _         stuck     = stuck
fmap2 f stuck     _         = stuck

mutual

  -- Values are either constants or closures
  data Value : Set where
    `Nat     : ℕ → Value
    `Bool    : Bool → Value
    `Closure : {n : ℕ} (b : Term (2 Nat.+ n)) (ρ : Valuation n) → Value

  Valuation : ℕ → Set
  Valuation = Vec Value

-- The outcome of the evaluation is a delayed result
Outcome : (i : Size) (A : Set) → Set
Outcome i A = [Delay i , Result A ]

result : {A B : Set} (a : A) (f : B → A) → Result B → A
result _ f (value a) = f a
result a f stuck     = a

-- We may expect nats
toNat : Result Value → Result ℕ
toNat (value (`Nat n)) = value n
toNat _                = stuck

toBool : Result Value → Result Bool
toBool (value (`Bool b)) = value b
toBool _                 = stuck

toClosure : Result Value → Result (Σ[ n ∈ ℕ ] Term (2 Nat.+ n) × Valuation n)
toClosure (value (`Closure b ρ)) = value (_ , b , ρ)
toClosure _                      = stuck

lift2[Delay] : {A B C : Set} {i : Size} (f : A → B → C) → [Delay i , A ] → [Delay i , B ] → [Delay i , C ]
lift2[Delay] f da db = (Delay.now! f ` Delay.[app] ` da) ` Delay.[app] ` db

lift2Value : {A : Set} (c : A → Value) (f : ℕ → ℕ → A) → Result Value → Result Value → Result Value
lift2Value c f v₁ v₂ = fmap2 (λ m → c ∘ f m) (toNat v₁) (toNat v₂)

-- Ops can be given a meaning 
δ : Op → {i : Size} → Outcome i Value → Outcome i Value → Outcome i Value
δ `+ = lift2[Delay] $ lift2Value `Nat Nat._+_
δ `- = lift2[Delay] $ lift2Value `Nat Nat._∸_
δ `* = lift2[Delay] $ lift2Value `Nat Nat._*_ 
δ `= = lift2[Delay] $ lift2Value `Bool $ λ m n → ⌊ m Nat.≟ n ⌋

-- evaluation is defined mutually with application
-- which restarts closures

mutual

  ⟦_⟧_ : {n : ℕ} {i : Size} (t : Term n) (ρ : Vec Value n) → Outcome i Value
  ⟦ `Nat n      ⟧ ρ = now! value (`Nat n)
  ⟦ `Bool b     ⟧ ρ = now! value (`Bool b)
  ⟦ `Op t op u  ⟧ ρ = δ op (⟦ t ⟧ ρ) (⟦ u ⟧ ρ)
  ⟦ `var k      ⟧ ρ = now! value (Vec.lookup k ρ)
  ⟦ `ifte b t f ⟧ ρ = [fmap] toBool (⟦ b ⟧ ρ) [>>=] result (now! stuck) (λ b → if b then ⟦ t ⟧ ρ else ⟦ f ⟧ ρ)
  ⟦ `rec t      ⟧ ρ = now! value (`Closure t ρ)
  ⟦ `app t u    ⟧ ρ = (lift2[Delay] _,_ (⟦ t ⟧ ρ) (⟦ u ⟧ ρ)) [>>=] uncurry ⟦app⟧

  ⟦app⟧ : {i : Size} → Result Value → Result Value → Outcome i Value
  ⟦app⟧ (value (`Closure b ρ)) (value val) = later beta b ρ val
  ⟦app⟧ _                      _           = now! stuck

  beta : {n : ℕ} {i : Size} → Term (2 Nat.+ n) → Valuation n → Value → Delay i (Result Value)
  force (beta b ρ v) = ⟦ b ⟧ (`Closure b ρ ∷ v ∷ ρ)

fact : ℕ → Outcome ∞ ℕ
fact n = [fmap] toNat $ ⟦ `app `fact (`Nat n) ⟧ []
  where
    `fact =
      `rec $
        let fact = `var Fin.zero
            n    = `var $ Fin.suc Fin.zero
        in `ifte (`Op n `= (`Nat 0))
                 (`Nat 1)
                 (`Op n `* (`app fact (`Op n `- (`Nat 1))))

ack : ℕ → ℕ → Outcome ∞ ℕ
ack m n = [fmap] toNat $ ⟦ `app (`app `ack (`Nat m)) (`Nat n) ⟧ []
  where
    `ack =
      `rec $ `rec $
        let ack = `var $ Fin.suc $ Fin.suc $ Fin.zero
            m   = `var $ Fin.suc $ Fin.suc $ Fin.suc $ Fin.zero
            n   = `var $ Fin.suc Fin.zero
        in `ifte (`Op m `= (`Nat 0))
                 (`Op n `+ (`Nat 1))
                 (`ifte (`Op n `= (`Nat 0))
                        (`app (`app ack (`Op m `- (`Nat 1))) (`Nat 1))
                        (`app (`app ack (`Op m `- (`Nat 1))) (`app (`app ack m) (`Op n `- (`Nat 1)))))

open import Data.Maybe

`06 : Maybe (Result ℕ)
`06 = run[Delay] 4 $ fact 3

`24 : Maybe (Result ℕ)
`24 = run[Delay] 5 $ fact 4

`5 : Maybe (Result ℕ)
`5 = run[Delay] 25 $ ack 3 0