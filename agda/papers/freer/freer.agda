module papers.freer.freer where

open import Level
open import Size
open import Function

open import Category.Functor
open import Category.Monad

open import Data.Unit as ⊤ using (⊤)
open import Data.Nat as ℕ using (ℕ)
open import Data.List as List using (List)
open import Data.Product as Prod using (_×_; _,_)
open import Codata.Stream as Stream using (Stream)

open import Algebra.Structures using (IsMonoid)
open import Relation.Binary using (Rel)

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

module Section-2-2 {i o} (I : Set i) (O : Set o) where

  data It {a} (A : Set a) : Set (i ⊔ o ⊔ a) where
    Pure : A → It A
    Get  : (I → It A) → It A
    Put  : O → (⊤ → It A) → It A

  infixl 1 _>>=_
  _>>=_ : ∀ {a b} {A : Set a} {B : Set b} →
          It A → (A → It B) → It B
  Pure a  >>= f = f a
  Get k   >>= f = Get $ λ i → k i >>= f
  Put o k >>= f = Put o $ λ u → k u >>= f

  module _ {e ε _∙_} {_≈_ : Rel O e} (𝕄 : IsMonoid _≈_ _∙_ ε) {a} {A : Set a} where

    runRdWriter : I → It A → (O × A)
    runRdWriter i = loop ε where

      loop : O → It A → (O × A)
      loop acc (Pure a)  = acc , a
      loop acc (Get k)   = loop acc (k i)
      loop acc (Put o k) = loop (acc ∙ o) (k ⊤.tt)

module Section-2-3 where

  {-# NO_POSITIVITY_CHECK #-}
  data Free {ℓ} (F : Set ℓ → Set ℓ) (i : Size) (A : Set ℓ) : Set ℓ where
    Pure   : A → Free F i A
    Impure : {j : Size< i} → F (Free F j A) → Free F i A


  monad : ∀ {ℓ} {F : Set ℓ → Set ℓ} → RawFunctor F → RawMonad (Free F ∞)
  monad {ℓ} {F} Fun = record
    { return = Pure
    ; _>>=_  = _>>=_
    } where

    open RawFunctor Fun

    _>>=_ : ∀ {A B : Set ℓ} {i} → Free F i A → (A → Free F ∞ B) → Free F ∞ B
    Pure a   >>= f = f a
    Impure e >>= f = Impure ((_>>= f) <$> e)

  data ReaderWriter {i o a} (I : Set i) (O : Set o) (A : Set a) : Set (i ⊔ o ⊔ a) where
    Get : (I → A)     → ReaderWriter I O A
    Put : O → (⊤ → A) → ReaderWriter I O A

  It : ∀ {i o a} (I : Set i) (O : Set o) → Set _ → Set _
  It {i} {o} {a} I O = Free {i ⊔ o ⊔ a} (ReaderWriter I O) ∞
