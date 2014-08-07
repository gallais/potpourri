module Comprehension where

open import Data.Product hiding (map)
open import Data.Nat
open import Data.List as List hiding (map ; concatMap ; [_])

open import Function
open import Relation.Nullary

-- DEFINING ENUMERATIONS (on ℕ but it could be used for anything enumerable)

≤′-trans : (m n p : ℕ) → m ≤′ n → n ≤′ p → m ≤′ p
≤′-trans m .m      p       ≤′-refl       le₂           = le₂
≤′-trans m n       .n      le₁           ≤′-refl       = le₁
≤′-trans m (suc n) (suc p) (≤′-step le₁) (≤′-step le₂) =
  ≤′-step (≤′-trans m (suc n) p (≤′-step le₁) le₂)

0≤′sn : (n : ℕ) → 0 ≤′ suc n
0≤′sn zero    = ≤′-step ≤′-refl
0≤′sn (suc n) = ≤′-step (0≤′sn n)

suc≤′ : (m n : ℕ) → m ≤′ n → suc m ≤′ suc n
suc≤′ m .m      ≤′-refl      = ≤′-refl
suc≤′ m (suc n) (≤′-step le) = ≤′-step (suc≤′ m n le)

suc≤′-inv : (m n : ℕ) → suc m ≤′ suc n → m ≤′ n
suc≤′-inv m .m      ≤′-refl          = ≤′-refl
suc≤′-inv m zero    (≤′-step ())
suc≤′-inv m (suc n) (≤′-step suc-le) =
  ≤′-trans m (suc m) (suc n) (≤′-step ≤′-refl) suc-le

_≤′?_ : (m n : ℕ) → Dec (m ≤′ n)
zero  ≤′? zero  = yes ≤′-refl
zero  ≤′? suc n = yes (0≤′sn n)
suc m ≤′? zero  = no (λ ())
suc m ≤′? suc n with m ≤′? n
... | yes pr = yes $ suc≤′ m n pr
... | no ¬pr = no  $ ¬pr ∘ (suc≤′-inv _ _)

enum : ℕ → ℕ → List ℕ
enum k l with k ≤′? l
... | no ¬pr = []
... | yes pr = enum-le k l pr []
  where
    enum-le : ∀ (k l : ℕ) (klel : k ≤′ l) (acc : List ℕ) → List ℕ
    enum-le k ._      ≤′-refl        acc = k ∷ acc
    enum-le k (suc l) (≤′-step klel) acc = enum-le k l klel (suc l ∷ acc)



-- SYNTAX DEFINITIONS FOR LIST COMPREHENSIONS

infixl 1 concatMap map
concatMap = List.concatMap
map       = List.map

[_] : ∀ {A : Set} → List A → List A
[_] x = x

-- Enumerations and binding
syntax enum k l = k ⋯ l
syntax map (λ x → expr) xs       = expr ∣ x ← xs
syntax concatMap (λ x → expr) xs = expr , x ← xs

[⟨2,3⟩,⟨4,6⟩,⟨6,9⟩,⋯,⟨10,15⟩] : List (ℕ × ℕ)
[⟨2,3⟩,⟨4,6⟩,⟨6,9⟩,⋯,⟨10,15⟩] = [ 2 * x , 3 * x ∣ x ← [ 1 ⋯ 5 ] ]

[x*y] : List ℕ
[x*y] = [ x * y ∣ x ← [ 1 ⋯ 5 ] , y ← [ 3 ⋯ 5 ] ]

myReplicate : (n : ℕ) {A : Set} (a : A) → List A
myReplicate n a = [ a ∣ x ← [ 1 ⋯ n ] ]

[6,24,⋯,150] : List ℕ
[6,24,⋯,150] = [ proj₁ x * proj₂ x ∣ x ← [⟨2,3⟩,⟨4,6⟩,⟨6,9⟩,⋯,⟨10,15⟩] ]

prod : List ℕ → ℕ
prod = foldl _*_ 1

[facts_] : ℕ → List ℕ
[facts n ] = [ prod [ 1 ⋯ k ] ∣ k ← [ 0 ⋯ n ] ]
-- [facts 500 ] computes in a just a few seconds!


example : List ℕ
example = [ x * y ∣ x ← 1 ∷ 2 ∷ 3 ∷ []
                 , y ← 2 ∷ 4 ∷ 6 ∷ [] ]
-- 2 ∷ 4 ∷ 6 ∷ 4 ∷ 8 ∷ 12 ∷ 6 ∷ 12 ∷ 18 ∷ []