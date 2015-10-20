{-# OPTIONS --copatterns #-}

module cyclicData where

open import Level using (Lift ; lower ; lift)
open import Size
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (lift)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

-- We start with the datatype of Descriptions and its usual
-- semantics as an endofunctor on Set. Given that this functor
-- is strictly positive, we can take its least and greatest
-- fixpoints:

data Desc : Set₁ where
  rec : Desc → Desc
  ret : Desc              
  arg : (A : Set) (d : A → Desc) → Desc

⟦_⟧ : (d : Desc) → Set → Set
⟦ rec d   ⟧ X = X × ⟦ d ⟧ X
⟦ ret     ⟧ X = ⊤
⟦ arg A d ⟧ X = Σ[ a ∈ A ] ⟦ d a ⟧ X

data μ (d : Desc) : Set where
  ⟨_⟩ : ⟦ d ⟧ (μ d) → μ d

record ν (d : Desc) (i : Size) : Set where
  coinductive
  field force : {j : Size< i} → ⟦ d ⟧ (ν d j)

-- But we can also give a non-standard interpretation of it as
-- an endofunctor on (ℕ → Set). This thing is once more strictly
-- positive so we could take its fixpoint. But we may as well
-- take advantage of the scope provided to us by the ℕ index: we
-- introduce a binder `fix⟨_⟩` and a variable `var`.
-- Elements of `μ′ d n` are finite representations of potentially
-- cyclic trees with `n` pointers in scope.

⟦_⟧′ : (d : Desc) → (ℕ → Set) → (ℕ → Set)
⟦ rec d   ⟧′ X n = X n × ⟦ d ⟧′ X n
⟦ ret     ⟧′ X n = ⊤
⟦ arg A d ⟧′ X n = Σ[ a ∈ A ] (⟦ d a ⟧′ X) n

data μ′ (d : Desc) (n : ℕ) : Set where
  fix⟨_⟩ : ⟦ d ⟧′ (μ′ d) (suc n) → μ′ d n
  ⟨_⟩    : ⟦ d ⟧′ (μ′ d) n       → μ′ d n
  var    : (k : Fin n)           → μ′ d n

-- It is rather natural to expose this structure by writing the
-- function unrolling the cycles to give rise to an inhabitant
-- of the corresponding greatest fixpoint:

Tel : Desc → ℕ → Set
Tel d zero    = Lift ⊤
Tel d (suc n) = ⟦ d ⟧′ (μ′ d) (suc n) × Tel d n

mutual

  unroll⟦⟧ : (e d : Desc) {n : ℕ} (t : Tel e n) (v : ⟦ d ⟧′ (μ′ e) n) {i : Size} → ⟦ d ⟧ (ν e i)
  unroll⟦⟧ e (rec d)   tel (r , v) = unrollν e tel r , unroll⟦⟧ e d tel v
  unroll⟦⟧ e ret       tel v       = tt
  unroll⟦⟧ e (arg A d) tel (a , v) = a , unroll⟦⟧ e (d a) tel v

  unrollν : (d : Desc) {n : ℕ} (t : Tel d n) (v : μ′ d n) {i : Size} → ν d i
  ν.force (unrollν d tel       fix⟨ v ⟩)      = unroll⟦⟧ d d (v , tel) v
  ν.force (unrollν d tel       ⟨ v    ⟩)      = unroll⟦⟧ d d tel v
  ν.force (unrollν d (v , tel) (var zero))    = unroll⟦⟧ d d (v , tel) v
  ν.force (unrollν d (_ , tel) (var (suc k))) = ν.force (unrollν d tel (var k))

unroll : {d : Desc} (r : μ′ d 0) → ν d ∞
unroll r = unrollν _ _ r

-- Greatest fixpoints are notoriously annoying to prove things
-- about. We can define bisimulation by first giving a relational
-- interpretation ⟦_⟧R for our Descriptions and then defining
-- `[_]_~_` as the appropriate greatest fixpoint.

Rel : Set → Set₁
Rel X = X → X → Set

⟦_⟧R : (d : Desc) {X : Set} (R : Rel X) → Rel (⟦ d ⟧ X)
⟦ rec d   ⟧R R (r₁ , e₁) (r₂ , e₂) = R r₁ r₂ × ⟦ d ⟧R R e₁ e₂
⟦ ret     ⟧R R tt        tt        = ⊤
⟦ arg A d ⟧R R (a₁ , e₁) (a₂ , e₂) = Σ[ eq ∈ a₁ ≡ a₂ ] ⟦ d a₁ ⟧R R e₁ (subst (λ a → ⟦ d a ⟧ _) (sym eq) e₂)

record [_]_~_ {d : Desc} (i : Size) (v w : ν d i) : Set where
  coinductive
  field force : {j : Size< i} → ⟦ d ⟧R [ j ]_~_ (ν.force v) (ν.force w)

-- Before looking at example, we introduce a handy combinator to
-- generate elements of `ν d i`: if we know how  to generate layer
-- after layer of `⟦ d ⟧`-things then we know how to generate an
-- element of `ν d i`.

pure : (d : Desc) {i : Size} (r : {X : Size → Set} → X i → ⟦ d ⟧ (X i)) → ν d i
ν.force (pure d r) = r (pure d r)

-------------------------------------------------
-- EXAMPLES
-------------------------------------------------

private

  -- We keep it simple and focus on the functor describing lists

  listD : Set → Desc
  listD A =
    arg Bool $ λ isNil? → case isNil? of λ
                            { true  → ret
                            ; false → arg A $ const $ rec ret
                            }
  -- It gives rise to three different type formers: the one for
  -- list, cyclic lists and colists respectively.

  list : Set → Set
  list = μ ∘ listD

  clist : Set → Set
  clist A = μ′ (listD A) 0

  colist : Set → Size → Set
  colist A = ν (listD A)

  -- We introduce some pattern synonyms to be able to have nice
  -- notations for our (c)lists.
  
  infixr 5 _∷_
  pattern nil      = ⟨ true , tt ⟩
  pattern _∷_ a as = ⟨ false , a , as , tt ⟩
  pattern rec[_∷_] a as = fix⟨ false , a , as , tt ⟩

  example : list ℕ
  example = 0 ∷ 1 ∷ 2 ∷ 3 ∷ nil

  czeros : clist ℕ
  czeros = rec[ 0 ∷ var zero ]

  zeros : {i : Size} → colist ℕ i
  zeros = pure _ $ λ r → false , 0 , r , tt

  -- Finally, we conclude with a proof that unfolding `czeros` leads
  -- to an infinite colist of 0s.

  equality : [ ∞ ] unroll czeros ~ zeros
  [_]_~_.force equality = refl , refl , go , tt

    where go : {i : Size} → [ i ] unrollν _ _ (var zero) ~ zeros
          [_]_~_.force go = refl , refl , go , tt
