module poc.DescSize where

open import Size
open import Data.Bool
open import Data.Nat hiding (_≤_ ; _≤′_ ; fold)
open import Data.Unit hiding (_≤_)
open import Data.Product hiding (,_)
open import Function hiding (_⟨_⟩_)

data Desc : Set₁ where
  `σ : (A : Set) (d : A → Desc) → Desc
  `r : Desc → Desc
  `ι : Desc

⟦_⟧ : Desc → (Size → Set) → (Size → Set)
⟦ `σ A d ⟧ X i = Σ[ a ∈ A ] ⟦ d a ⟧ X i
⟦ `r d   ⟧ X i = X i × ⟦ d ⟧ X i
⟦ `ι     ⟧ X i = ⊤

data μ (d : Desc) : Size → Set where
  ⟨_⟩ : {i : Size} → ⟦ d ⟧ (μ d) i → μ d (↑ i)


_≤_ : (X Y : Size → Set) → Size → Set
X ≤ Y = λ i → X i → Y (↑ i)

_≤′_ : (X Y : Size → Set) → Set
X ≤′ Y = {i : Size} → X i → Y (↑ i)

_⟶_ : (X Y : Size → Set) → Size → Set
X ⟶ Y = λ i → X i → Y i

_⟶′_ : (X Y : Size → Set) → Set
X ⟶′ Y = ∀ {i} → X i → Y i

fmap : ∀ {X Y} (d : Desc) → (X ⟶ Y) ⟶′ (⟦ d ⟧ X ⟶ ⟦ d ⟧ Y)
fmap {X} {Y} d {i} f = go d where

  go : (d : Desc) → ⟦ d ⟧ X i → ⟦ d ⟧ Y i
  go (`σ A d) (a , t) = a , go (d a) t
  go (`r d)   (x , t) = f x , go d t
  go `ι       tt      = tt

fold : ∀ {d} X → (⟦ d ⟧ X ≤′ X) → (μ d ⟶′ X)
fold {d} X alg = go where

  go : μ d ⟶′ X
  go ⟨ t ⟩ = alg (fmap d go t)

id′ : ∀ {d} → μ d ⟶′ μ d
id′ t = fold (μ _) ⟨_⟩ t


------------ Lists
listD : Set → Desc
listD A = `σ Bool $ λ b →
          if b then `ι
          else `σ A (const $ `r `ι)

pattern nil       = (true , tt)
pattern cons x xs = (false , (x , xs , tt))

pattern nil′       = ⟨ nil ⟩
pattern cons′ x xs = ⟨ cons x xs ⟩

list₀₁ : μ (listD ℕ) _
list₀₁ = cons′ 0 (cons′ 1 nil′)

list₂₃ : μ (listD ℕ) _
list₂₃ = cons′ 2 (cons′ 3 nil′)

append : {A : Set} → μ (listD A) ∞ → μ (listD A) ∞ → μ (listD A) ∞
append {A} xs ys = fold goal alg xs ys where

  goal : Size → Set
  goal _ = μ (listD A) ∞ → μ (listD A) ∞

  alg : ⟦ listD A ⟧ goal ≤′ goal
  alg nil         = id
  alg (cons x xs) = cons′ x ∘ xs

reverse : {A : Set} → μ (listD A) ∞ → μ (listD A) ∞
reverse {A} xs = fold goal alg xs nil′ where

  goal : Size → Set
  goal _ = μ (listD A) ∞ → μ (listD A) ∞

  alg : ⟦ listD A ⟧ goal ≤′ goal
  alg nil         = id
  alg (cons x xs) = xs ∘ cons′ x

list : μ (listD ℕ) _
list = append list₀₁ list₂₃

------------ Binary Trees
treeD : Set → Desc
treeD A = `σ Bool $ λ b →
          if b then `σ A (const `ι)
          else `r (`r `ι)

pattern leaf l   = (true , (l , tt))
pattern node l r = (false , (l , r , tt))

pattern leaf′ l   = ⟨ leaf l ⟩
pattern node′ l r = ⟨ node l r ⟩

tree : μ (treeD ℕ) _
tree = node′ (node′ (leaf′ 0) (leaf′ 1)) (node′ (leaf′ 2) (leaf′ 3))

depth : ∀ {A} → μ (treeD A) ⟶′ const ℕ
depth {A} = fold (const ℕ) alg where

  alg : ⟦ treeD A ⟧ (const ℕ) ≤′ const ℕ
  alg (leaf _)   = 0
  alg (node l r) = 1 + l ⊔ r

leaves : ∀ {A} → μ (treeD A) ∞ → μ (listD A) ∞
leaves {A} = fold goal alg where

  goal : Size → Set
  goal _ = μ (listD A) ∞

  alg : ⟦ treeD A ⟧ goal ≤′ goal
  alg (leaf l)   = cons′ l nil′
  alg (node l r) = append l r

mirror : ∀ {A} → μ (treeD A) ⟶′ μ (treeD A)
mirror {A} = fold (μ (treeD A)) alg where

  alg : ⟦ treeD A ⟧ (μ (treeD A)) ≤′ μ (treeD A)
  alg (leaf l)   = leaf′ l
  alg (node l r) = node′ r l

open import Relation.Binary.PropositionalEquality

tests : depth (node′ tree (leaf′ 1)) ≡ 3
      × leaves tree ≡ list
      × leaves (mirror tree) ≡ reverse list
tests = refl , refl , refl
