{-# OPTIONS --without-K #-}

module Coverage where

open import Data.Unit.Base
open import Data.Empty

open import Data.List.Base using (List; []; _∷_)
import Data.List.Effectful as List
open import Data.List.Relation.Unary.All as List using ([]; _∷_)
open import Data.List.Relation.Unary.Any as List using (here; there)

open import Data.List.NonEmpty.Base using (List⁺; _∷_; toList)
import Data.List.NonEmpty.Effectful as List⁺
open import Data.List.NonEmpty.Relation.Unary.Any as List⁺ using (here; there)

open import Data.Product as Prod using (_×_; _,_; Σ-syntax; proj₁)
import Data.Product.Relation.Unary.All as Prod
open import Data.String using (String; _≟_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.These.Base
open import Data.These.Relation.Unary.Any as These using (this; that; these₁; these₂)

open import Effect.Applicative using (module RawApplicative; module RawAlternative)

open import Function.Base using (id; const; _∘_; case_of_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)

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
⟦ `X            ⟧ X = X
⟦ `AtomBar ats  ⟧ X = Σ[ at ∈ String ] List.All (at ≢_) ats
⟦ `Prod d₁ d₂   ⟧ X = ⟦ d₁ ⟧ X × ⟦ d₂ ⟧ X
⟦ `EnumOrTag ds ⟧ X
  = These.Any
      (List⁺.Any Singleton)
      (List⁺.Any (Prod.All Singleton λ d → ⟦ d ⟧ X))
      ds

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

data Pat (d : Desc) : (e : Desc) → Set where
  `var : ∀ {e} → Pat d e
  `at : ∀ {ats} (str : String) → List.All (str ≢_) ats → Pat d (`AtomBar ats)
  `et : ∀ {ds} →
        These.Any
          (List⁺.Any Singleton)
          (List⁺.Any (Prod.All Singleton (Pat d)))
          ds →
        Pat d (`EnumOrTag ds)
  `prd : ∀ {e₁ e₂} → Pat d e₁ → Pat d e₂ → Pat d (`Prod e₁ e₂)
  `in : Pat d d → Pat d `X

data _≤_ : {d e : Desc} → (p q : Pat d e) → Set where
  `invar : ∀ {d} {p : Pat d d} → p ≤ `var → `in p ≤ `var
  -- structural rules
  `var : ∀ {d e} → `var {d} {e} ≤ `var
  `at : ∀ {d ats} str {p q} → `at {d} {ats} str p ≤ `at str q
  `in : ∀ {d} {p q : Pat d d} → p ≤ q → `in p ≤ `in q

refl : ∀ {d e} {p : Pat d e} → p ≤ p
refl = {!!}

irrelevant : ∀ {str : String} {ats} {p q : List.All (str ≢_) ats} → p ≡ q
irrelevant {p = []} {[]} = P.refl
irrelevant {p = _ ∷ p} {_ ∷ q} = P.cong (_ ∷_) irrelevant

{-
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
-}

module _ (ini d : Desc) where

  Sound : (partition : List⁺ Desc × List Desc) → Set
  Sound (t , l) = List⁺.Any (Pat ini) t ⊎ List.Any (Pat ini) l → Pat ini d
   -- this should actually be 'at least one' rather than 'any' :((

  Complete : (partition : List⁺ Desc × List Desc) (sound : Sound partition) → Set
  Complete (t , l) sound
    = (p : Pat ini d)
    →  Σ[ p′ ∈ List⁺.Any (Pat ini) t ] sound (inj₁ p′) ≤ p
    ⊎  Σ[ p′ ∈ List.Any (Pat ini) l ] sound (inj₂ p′) ≤ p

  record Split : Set where
    field
      partition : List⁺ Desc × List Desc
      sound     : Sound partition
      complete  : Complete partition sound
  open Split public

_\\_  : ∀ {ini} (d : Desc) (p : Pat ini d) → Split ini d

{-
_\\μ_ : ∀ ini (p : μPat ini) → μSplit ini
ini \\μ `in p = let spl = ini \\ p in record
  { partition = Split.partition spl
  ; sound = `in ∘ Split.sound spl
  ; complete = λ where
    (`in p) → Sum.map (Prod.map₂ (cong `in)) (Prod.map₂ (cong `in))
              (Split.complete spl p) }
-}

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
    `var → inj₂ (here `var , `var)
    (`at str neq) → case str ≟ at of λ where
      (yes P.refl) → inj₁ (here (`et (this (here mkSingleton))), `at at)
      (no ¬eq) → inj₂ (here (`at str (¬eq ∷ neq)) , `at str) }
`EnumOrTag ds \\ `et x = {!!}
`Prod d₁ d₂ \\ `prd p₁ p₂
  = let spl₁ = d₁ \\ p₁ ; spl₂ = d₂ \\ p₂ in record
  { partition
    = let (t₁ , l₁) = partition spl₁ in
      let (t₂ , l₂) = partition spl₂ in
      (let open RawApplicative List⁺.applicative in ⦇ `Prod t₁ t₂ ⦈ )
    , (let open RawAlternative List.alternative in
       ⦇ `Prod (toList t₁) l₂ | `Prod l₁ (toList t₂) | `Prod l₁ l₂ ⦈)
  ; sound = {!!}
  ; complete = {!!}
  }
`X \\ `in p = let spl = _ \\ p in record
  { partition = partition spl
  ; sound = λ p → `in (sound spl p)
  ; complete = λ where
    `var → Sum.map (Prod.map₂ `invar) (Prod.map₂ `invar) (complete spl `var)
    (`in p) → Sum.map (Prod.map₂ `in) (Prod.map₂ `in) (complete spl p) }

coverage : ∀ {ini d} → List⁺ (Pat ini d) → Pat ini d ⊎ Split ini d
coverage {ini} {d} (p ∷ ps) = go (_ \\ p) ps where

  go : Split ini d → List (Pat ini d) → Pat ini d ⊎ Split ini d
  go spl [] = inj₂ spl
  go spl (p ∷ ps) = case complete spl p of λ where
    (inj₁ _) → inj₁ p
    (inj₂ (p′ , snd)) → {!!}

test : coverage {ini = Tree} {d = Tree} (`var ∷ `et (these₁ (here mkSingleton)) ∷ [])
     ≡ inj₁ (`et (these₁ (here mkSingleton))) -- already covered by `var
test = P.refl


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
