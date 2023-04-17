{-# OPTIONS --without-K #-}

module Coverage where

open import Data.Unit.Base
open import Data.Empty
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as List using ([]; _∷_)
open import Data.List.Relation.Unary.Any as List using (here; there)
open import Data.List.NonEmpty.Base
open import Data.List.NonEmpty.Relation.Unary.Any as List⁺ using (here; there)
open import Data.Product as Prod
import Data.Product.Relation.Unary.All as Prod
open import Data.String using (String; _≟_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.These.Base
open import Data.These.Relation.Unary.Any as These using (this; that; these₁; these₂)
open import Function.Base
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data Singleton {a} {A : Set a} (x : A) : Set where
  mkSingleton : Singleton x

data Desc : Set where
  `AtomBar : List String → Desc
  `Prod : Desc → Desc → Desc
  `EnumOrTag : These (List⁺ String) (List⁺ (String × Desc)) → Desc
  `X : Desc

pattern `Atom = `AtomBar []

{-# TERMINATING #-}
⟦_⟧ : Desc → Set → Set
⟦ `AtomBar ats  ⟧ X = Σ[ at ∈ String ] List.All (at ≢_) ats
⟦ `Prod d₁ d₂   ⟧ X = ⟦ d₁ ⟧ X × ⟦ d₂ ⟧ X
⟦ `EnumOrTag ds ⟧ X
  = These.Any
      (List⁺.Any Singleton)
      (List⁺.Any (Prod.All Singleton λ d → ⟦ d ⟧ X))
      ds
⟦ `X            ⟧ X = X

data `μ (d : Desc) : Set where
  `in : ⟦ d ⟧ (`μ d) → `μ d

Tree : Desc
Tree = `EnumOrTag (these ("leaf" ∷ []) (("node" , `Prod `X (`Prod `Atom `X)) ∷ []))

leaf : `μ Tree
leaf = `in (these₁ (here mkSingleton))

node : `μ Tree → String → `μ Tree → `μ Tree
node l v r = `in (these₂ (here (mkSingleton , l , (v , []) , r)))

example : `μ Tree
example = node (node leaf "hello" leaf) " " (node (node leaf "world" leaf) "!" leaf)

data μPat (d : Desc) : Set
data Pat (d : Desc) : (e : Desc) → Set

data μPat d where
  `in : Pat d d → μPat d

data Pat d where
  `var : ∀ {e} → Pat d e
  `at : ∀ {ats} (str : String) → List.All (str ≢_) ats → Pat d (`AtomBar ats)
  `et : ∀ {ds} →
        These.Any
          (List⁺.Any Singleton)
          (List⁺.Any (Prod.All Singleton (Pat d)))
          ds →
        Pat d (`EnumOrTag ds)
  _`,_ : ∀ {e₁ e₂} → Pat d e₁ → Pat d e₂ → Pat d (`Prod e₁ e₂)
  `rec : μPat d → Pat d `X

irrelevant : ∀ {str : String} {ats} {p q : List.All (str ≢_) ats} → p ≡ q
irrelevant {p = []} {[]} = refl
irrelevant {p = _ ∷ p} {_ ∷ q} = cong (_ ∷_) irrelevant

module _ (ini : Desc) where

  μSound : (partition : List⁺ Desc × List Desc) → Set
  μSound (t , l) = List⁺.Any (Pat ini) t ⊎ List.Any (Pat ini) l → μPat ini

  μComplete : (partition : List⁺ Desc × List Desc) (sound : μSound partition) → Set
  μComplete (t , l) sound
    = (p : μPat ini)
    → Σ[ p′ ∈ List⁺.Any (Pat ini) t ] p ≡ sound (inj₁ p′)
    ⊎ Σ[ p′ ∈ List.Any (Pat ini) l ] p ≡ sound (inj₂ p′)

  record μSplit : Set where
    field
      partition : List⁺ Desc × List Desc
      sound     : μSound partition
      complete  : μComplete partition sound
  open μSplit

module _ (ini d : Desc) where

  Sound : (partition : List⁺ Desc × List Desc) → Set
  Sound (t , l) = List⁺.Any (Pat ini) t ⊎ List.Any (Pat ini) l → Pat ini d

  Complete : (partition : List⁺ Desc × List Desc) (sound : Sound partition) → Set
  Complete (t , l) sound
    = (p : Pat ini d)
    → Σ[ p′ ∈ List⁺.Any (Pat ini) t ] p ≡ sound (inj₁ p′)
    ⊎ Σ[ p′ ∈ List.Any (Pat ini) l ] p ≡ sound (inj₂ p′)

  record Split : Set where
    field
      partition : List⁺ Desc × List Desc
      sound     : Sound partition
      complete  : Complete partition sound
  open Split

_\\_  : ∀ {ini} (d : Desc) (p : Pat ini d) → Split ini d

_\\μ_ : ∀ ini (p : μPat ini) → μSplit ini
ini \\μ `in p = let spl = ini \\ p in record
  { partition = Split.partition spl
  ; sound = `in ∘ Split.sound spl
  ; complete = λ where
    (`in p) → Sum.map (Prod.map₂ (cong `in)) (Prod.map₂ (cong `in))
              (Split.complete spl p) }

d \\ `var = record
  { partition = d ∷ [] , []
  ; sound = λ where (inj₁ (here p)) → p
  ; complete = λ p → inj₁ (here p , refl) }
`AtomBar ats \\ `at at neq = record
  { partition = `EnumOrTag (this (at ∷ [])) ∷ [] , `AtomBar (at ∷ ats) ∷ []
  ; sound = λ where
    (inj₁ (here `var)) → `var
    (inj₁ (here (`et p))) → `at at neq
    (inj₂ (here `var)) → `var
    (inj₂ (here (`at str (_ ∷ neq)))) → `at str neq
  ; complete = λ where
    `var → inj₂ (here `var , refl)
    (`at str neq) → case str ≟ at of λ where
      (yes refl) → inj₁ (here (`et (this (here mkSingleton))) , cong (`at at) irrelevant)
      (no ¬eq) → inj₂ ((here (`at str (¬eq ∷ neq))) , refl) }
`EnumOrTag ds \\ `et x = {!!}
`Prod d e \\ (p `, p₁) = {!!}
`X \\ `rec p = let spl = _ \\μ p in record
  { partition = μSplit.partition spl
  ; sound = `rec ∘ μSplit.sound spl
  ; complete = λ where
    `var → inj₁ (here `var , {!!})
    (`rec x) → {!!} }


{-
{-
split : ∀ {ini} d (p : Pat ini d) → Split ini d

spl \\ p with complete spl p
... | inj₁ (p′ , refl) = fail p′
... | inj₂ (p′ , eq) = {!!}

split d `var = record
  { taken = d
  ; leftover = `⊥
  ; sound = [ id , absurd ]′
  ; complete = λ p → inj₁ (p , refl) }
split `⊤ `tt = record
  { taken = `⊤
  ; leftover = `⊥
  ; sound = [ id , absurd ]′
  ; complete = λ p → inj₁ (p , refl) }
split (d₁ `+ d₂) (`inj₁ p) = let spl′ = split d₁ p in record
  { taken = taken spl′ `+ `⊥
  ; leftover = leftover spl′ `+ d₂
  ; sound = [ (λ where
                   `var → `var
                   (`inj₁ p′) → `inj₁ (sound spl′ (inj₁ p′))
                   (`inj₂ p′) → absurd p′)
            , (λ where
                   `var → `var
                   (`inj₁ p′) → `inj₁ (sound spl′ (inj₂ p′))
                   (`inj₂ p′) → `inj₂ p′)
            ]′
  ; complete = λ where
     `var → {!!}
     (`inj₁ p) → {!!}
     (`inj₂ p) → inj₂ (`inj₂ p , refl)
  }
split (d₁ `+ d₂) (`inj₂ p) = {!!}
split (d₁ `× d₂) (p `, q) = {!!}
split `X (`rec x) = {!!}
-}
-}
