-- The content of this module is based on the paper
-- "Universes for Generic Programs and Proofs in Dependent Type Theory"
-- by Marcin Benke, Peter Dybjer, and Patrik Jansson

module papers.ugpp03.ugpp03 where

import Level as L
open import Agda.Builtin.Nat hiding (_+_)
open import Agda.Builtin.List
open import Agda.Builtin.Size

data 𝟘 : Set where
record 𝟙 : Set where constructor <>

infixr 5 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B

infixr 4 _+_
data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

record RawFunctor (F : Set → Set) : Set₁ where
  field map : ∀ {X Y} → (X → Y) → (F X → F Y)
open RawFunctor {{...}} public

record RawBiFunctor (F : Set → Set → Set) : Set₁ where
  field bimap : ∀ {A B X Y} → (A → B) → (X → Y) → (F A X → F B Y)
open RawBiFunctor {{...}} public

instance

  bif-× : RawBiFunctor _×_
  RawBiFunctor.bimap bif-× f g (a , x) = f a , g x

  bif-+ : RawBiFunctor _+_
  RawBiFunctor.bimap bif-+ f g (inl a) = inl (f a)
  RawBiFunctor.bimap bif-+ f g (inr x) = inr (g x)

infixl 6 _^_
_^_ : Set → Nat → Set
X ^ zero  = 𝟙
X ^ suc n = X × X ^ n

record RawFoldable ℓ (F : Set → Set) : Set (L.suc ℓ) where
  field fold : ∀ {X} {Y : Set ℓ} → Y → (X → Y → Y) → F X → Y
open RawFoldable {{...}}

instance

  f-^ : ∀ n → RawFunctor (_^ n)
  RawFunctor.map (f-^ zero)    f = λ x → x
  RawFunctor.map (f-^ (suc n)) f = bimap f (map {{f-^ n}} f)

  fd-^ : ∀ {ℓ} n → RawFoldable ℓ (_^ n)
  RawFoldable.fold (fd-^ zero)    y c <>       = y
  RawFoldable.fold (fd-^ (suc n)) y c (x , xs) = c x (fold {{fd-^ n}} y c xs)

All : ∀ {F X} (P : X → Set) {{rf : RawFoldable _ F}} → F X → Set
All P = fold 𝟙 (λ x → P x ×_)

module section1 where

  Sig : Set
  Sig = List Nat

  ⟦_⟧ : Sig → Set → Set
  ⟦ []    ⟧ X = 𝟘
  ⟦ n ∷ Σ ⟧ X = X ^ n + ⟦ Σ ⟧ X

  instance

     f-Sig : ∀ Σ → RawFunctor (⟦ Σ ⟧)
     RawFunctor.map (f-Sig [])      f = λ ()
     RawFunctor.map (f-Sig (n ∷ Σ)) f = bimap (map f) (map {{f-Sig Σ}} f)

  data T (Σ : Sig) : Size → Set where
    <_> : ∀ {i} → ⟦ Σ ⟧ (T Σ i) → T Σ (↑ i)

  iter : ∀ {Σ C i} → (⟦ Σ ⟧ C → C) → T Σ i → C
  iter alg < t > = alg (map {F = ⟦ _ ⟧} (iter alg) t)

  instance

    fd-Sig : ∀ ℓ Σ → RawFoldable ℓ ⟦ Σ ⟧
    RawFoldable.fold (fd-Sig ℓ [])      y c ()
    RawFoldable.fold (fd-Sig ℓ (n ∷ Σ)) y c (inl x) = fold {F = _^ n}  y c x
    RawFoldable.fold (fd-Sig ℓ (n ∷ Σ)) y c (inr v) = fold {{fd-Sig ℓ Σ}} y c v

  induction : ∀ {Σ i} (P : T Σ ω → Set) →
              (∀ {i} (t : ⟦ Σ ⟧ (T Σ i)) → All {F = ⟦ Σ ⟧} P t → P < t >) →
              (t : T Σ i) → P t
  induction P alg < t > = alg t {!!}
