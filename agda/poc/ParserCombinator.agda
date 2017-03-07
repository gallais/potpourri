module poc.ParserCombinator where

open import Data.Nat
open import Data.Sum as S
open import Data.Product as P

infixr 2 _⟶_
_⟶_ : (A B : ℕ → Set) → (ℕ → Set)
(A ⟶ B) n = A n → B n

infixr 3 _⊕_
_⊕_ : (A B : ℕ → Set) → (ℕ → Set)
(A ⊕ B) n = A n ⊎ B n

infixr 4 _⊗_
_⊗_ : (A B : ℕ → Set) → (ℕ → Set)
(A ⊗ B) n = A n × B n

infix 3 □_
□_ : (A : ℕ → Set) → (ℕ → Set)
(□ A) n = ∀ m → .(m < n) → A m

infix 4 [_]
[_] : (A : ℕ → Set) → Set
[ A ] = ∀ {n} → A n

open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Maybe as M
open import Data.Char
open import Data.Nat.Properties
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable

∣_∣≡_ : {A : Set} → List A → ℕ → Set
∣ [] ∣≡ zero = ⊤
∣ [] ∣≡ suc n = ⊥
∣ x ∷ xs ∣≡ zero = ⊥
∣ x ∷ xs ∣≡ suc n = ∣ xs ∣≡ n

trivial : {A : Set} (xs : List A) → ∣ xs ∣≡ length xs
trivial [] = tt
trivial (x ∷ xs) = trivial xs

record Vec (A : Set) (n : ℕ) : Set where
  constructor mkVec
  field elements : List A
        .prf     : ∣ elements ∣≡ n
open Vec

data View (A : Set) : (n : ℕ) → Vec A n → Set where
  nil  : View A 0 (mkVec [] _)
  cons : ∀ {n} a (as : Vec A n) .{e} → View A (suc n) (mkVec (a ∷ elements as) e)

vec : ∀ {n} {A} (xs : Vec A n) → View A n xs
vec {zero}  (mkVec [] _) = nil
vec {suc n} (mkVec (x ∷ xs) prf) = cons x (mkVec xs prf)
vec {zero}  (mkVec (_ ∷ _) ())
vec {suc n} (mkVec [] ())

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s le₁) (s≤s le₂) = s≤s (≤-trans le₁ le₂)

run : {A : ℕ → Set} → [ □ A ] → [ A ]
run a {n} = a {suc n} n ≤-refl 

String = Vec Char

<⇒≤ : ∀ {m n} → m < n → m ≤ n
<⇒≤ = ≤-trans (n≤1+n _)

record Parser (A : Set) (n : ℕ) : Set where
  constructor mkParser
  field runParser : ∀ {m} → .(m ≤ n) → String m → Maybe (A × ∃ λ p → p < m × String p)
open Parser

open import Function

infixr 5 _<$>_
_<$>_ : {A B : Set} → (A → B) → [ Parser A ⟶ Parser B ]
runParser (f <$> p) lt s = M.map (P.map f id) (runParser p lt s)

infixr 5 _<$_
_<$_ : {A B : Set} → B → [ Parser A ⟶ Parser B ]
b <$ p = const b <$> p

return : {A : Set} → [ Parser A ⟶ □ Parser A ]
runParser (return p lt le) s = runParser p (≤-trans s (<⇒≤ le))

fix□ : {A : Set} → [ (□ Parser A ⟶ Parser A) ] → [ □ Parser A ]
fix□ f {zero}  = λ _ ()
fix□ f {suc n} = λ m m<sn → f (λ p p<m → fix□ f p (≤-trans p<m (≤-pred m<sn)))

fix : {A : Set} → [ (□ Parser A ⟶ Parser A) ] → [ Parser A ]
fix = run ∘ fix□

open import Relation.Nullary

char : Char → [ Parser Char ]
runParser (char c) lt s with vec s
... | nil       = nothing
... | cons a as with a Data.Char.≟ c
runParser (char c) lt _ | cons a as | yes p = just (c , _ , ≤-refl , as)
runParser (char c) lt _ | cons a as | no ¬p = nothing

open import Category.Monad
import Level
open RawMonad (M.monad {Level.zero}) using (_>>=_)

infixl 4 _<&>_
_<&>_ : {A B : Set} → [ Parser A ⟶ □ Parser B ⟶ Parser (A × B) ]
runParser (A <&> B) m≤n s =
  runParser A m≤n s >>= λ rA →
  let (a , p , p<m , s′) = rA in
  runParser (B p (≤-trans p<m m≤n)) ≤-refl s′ >>= λ rB →
  let (b , q , q<p , s′′) = rB in
  just ((a , b) , q , <-trans q<p p<m , s′′)

infixr 3 _<|>_
_<|>_ : {A B : Set} → [ Parser A ⟶ Parser B ⟶ Parser (A ⊎ B) ]
runParser (A <|> B) m≤n s with runParser (inj₁ <$> A) m≤n s
... | nothing = runParser (inj₂ <$> B) m≤n s
... | r = r

Nat : [ Parser ℕ ]
Nat = fix (λ r → [ id , suc ∘ proj₂ ]′ <$> (0 <$ char 'Z' <|> char 'S' <&> r))

import Data.String as String
open String using () renaming (String to Text)

`_ : (s : Text) → String (length (String.primStringToList s))
` s = let xs = String.primStringToList s in mkVec xs (trivial xs)

data Singleton {A : Set} : A → Set where
  _! : (a : A) → Singleton a

_∈_ : {A : Set} → Text → [ Parser A ] → Set
s ∈ A with runParser A (n≤1+n _) (` s)
s ∈ A | just (a , 0 , _ , _)  = Singleton a
s ∈ A | _ = ⊥

_ : "Z" ∈ Nat
_ = 0 !

_ : "SSSSSZ" ∈ Nat
_ = 5 !


data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

BTree : {A : Set} → [ Parser A ] → [ Parser (Tree A) ]
BTree A = fix (λ r → [ leaf ∘ proj₂ , uncurry (node ∘ proj₂) ]′
                 <$> (char 'L' <&> return A <|> char 'N' <&> r <&> r))

_ : "NNLZLSSZLZ" ∈ BTree Nat
_ = node (node (leaf 0) (leaf 2)) (leaf 0) !

_ : "NNLZLSSZNLZLSSSZ" ∈ BTree Nat
_ = node (node (leaf 0) (leaf 2)) (node (leaf 0) (leaf 3)) !
