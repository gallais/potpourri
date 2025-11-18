open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head; tail)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤)
open import Function.Base using (id; const; _∘_; _$_)
open import Relation.Unary using (IUniversal; _⇒_)

data IDesc (I O : Set) : Set₁ where
  `ret : (o : O) → IDesc I O
  `Π   : (A : Set) (d : A → IDesc I O) → IDesc I O
  `rec : (i : I) → IDesc I O → IDesc I O

`node : IDesc ⊤ ⊤
`node = `rec _ $ `rec _ $ `rec _ $ `rec _ $ `ret _

variable
  I O : Set
  X : I → Set
  Y : O → Set
  A : I → Set
  B : O → Set

Algᵒ : IDesc I O → (I → Set) → (O → Set) → Set
Algᵒ (`ret o)   X Y = Y o
Algᵒ (`Π A d)   X Y = (a : A)  → Algᵒ (d a) X Y
Algᵒ (`rec i d) X Y =      X i → Algᵒ d     X Y

bimap : ∀[ A ⇒ X ]
      → ∀[ Y ⇒ B ]
      → (d : IDesc I O)
      → Algᵒ d X Y → Algᵒ d A B
bimap f g (`ret o)   α = g α
bimap f g (`Π A d)   α = λ a → bimap f g (d a) (α a)
bimap f g (`rec i d) α = λ r → bimap f g d (α (f r))


module App
  (F : Set → Set)
  (pure : ∀ {A} → A → F A)
  (_<*>_ : ∀ {A B} → F (A → B) → F A → F B)
  where

  LiftA : ∀ (I O : Set) (X : I → Set) (Y : O → Set) → Set₁
  LiftA I O X Y = (d : IDesc I O) → Algᵒ d X Y → Algᵒ d (F ∘ X) (F ∘ Y)

  liftAˡ : LiftA I O X Y
  liftAˡ d = go d ∘ pure where

    go : (d : IDesc I O)
       → F (Algᵒ d X Y)
       → Algᵒ d (F ∘ X) (F ∘ Y)
    go (`ret o)   α = α
    go (`Π A d)   α = λ a → go (d a) (pure (_$ a) <*> α)
    go (`rec i d) α = λ fx → go d (α <*> fx)

  liftAʳ : LiftA I O X Y
  liftAʳ d α = go d (λ _ → α) [] where

    sequence : ∀ {xs} → All (F ∘ X) xs → F (All X xs)
    sequence [] = pure []
    sequence (fx ∷ fxs) = (pure _∷_ <*> fx) <*> sequence fxs

    go : (d : IDesc I O)
       → {is : List I}
       → (All     X  is → Algᵒ d      X       Y)
       → All (F ∘ X) is → Algᵒ d (F ∘ X) (F ∘ Y)
    go (`ret o)   α fxs = pure α <*> sequence fxs
    go (`Π A d)   α fxs = λ a → go (d a) (λ xs → α xs a) fxs
    go (`rec i d) α fxs = λ fx → go d (λ xxs → α (tail xxs) (head xxs)) (fx ∷ fxs)


open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open App (List ℕ ×_) ([] ,_) (λ (bs1 , f) (bs2 , x) → (bs1 ++ bs2 , f x))

alg : Algᵒ `node (const ⊤) (const ⊤)
alg = λ _ _ → _

test : LiftA ⊤ ⊤ (const ⊤) (const ⊤) → List ℕ
test liftA = proj₁ $ liftA `node alg (0 ∷ [] , _) (1 ∷ [] , _) (2 ∷ [] , _) (3 ∷ [] , _)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

_ : test liftAˡ ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
_ = refl

_ : test liftAʳ ≡ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []
_ = refl
