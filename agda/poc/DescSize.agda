module poc.DescSize where

open import Size
open import Data.Unit hiding (_≤_)
open import Data.Product

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

fold : ∀ d X → (⟦ d ⟧ X ≤′ X) → (μ d ⟶′ X)
fold d X alg = go where

  go : μ d ⟶′ X
  go ⟨ t ⟩ = alg (fmap d go t)

id : ∀ d → μ d ⟶′ μ d
id d t = fold d (μ d) ⟨_⟩ t
