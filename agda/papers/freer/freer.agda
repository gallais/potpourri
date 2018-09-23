module papers.freer.freer where

open import Level
open import Size
open import Function
open import Data.Nat as ℕ using (ℕ)
open import Data.List as List using (List)
open import Data.Product as Prod using (_,_)
open import Codata.Stream as Stream using (Stream)

module Section-2-1 where

  data It {i a} (I : Set i) (A : Set a) : Set (i ⊔ a) where
    Pure : A → It I A
    Get  : (I → It I A) → It I A

  ask : ∀ {i} {I : Set i} → It I I
  ask = Get Pure

  pure : ∀ {i a} {I : Set i} {A : Set a} → A → It I A
  pure = Pure

  infixl 1 _>>=_ _>>>_
  _>>=_ : ∀ {i a b} {I : Set i} {A : Set a} {B : Set b} →
          It I A → (A → It I B) → It I B
  Pure a >>= f = f a
  Get k  >>= f = Get $ λ i → k i >>= f

  _>>>_ : ∀ {i a b c} {I : Set i} {A : Set a} {B : Set b} {C : Set c} →
          (A → It I B) → (B → It I C) → A → It I C
  (f >>> g) a = f a >>= g


  addGet : ℕ → It ℕ ℕ
  addGet x = ask >>= λ i → pure (i ℕ.+ x)

  addN : ℕ → It ℕ ℕ
  addN n = List.foldr _>>>_ pure (List.replicate n addGet) 0

  runReader : ∀ {i a} {I : Set i} {A : Set a} → I → It I A → A
  runReader i (Pure a) = a
  runReader i (Get k)  = runReader i (k i)

  feedAll : ∀ {i a} {I : Set i} {A : Set a} →
            Stream I ∞ → It I A → A
  feedAll is (Pure a) = a
  feedAll is (Get k)  = let (i , is′) = Stream.uncons is in feedAll is′ (k i)


