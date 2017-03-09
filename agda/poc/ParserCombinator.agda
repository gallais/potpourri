module poc.ParserCombinator where

open import Data.Nat
open import Data.Sum as S
open import Data.Product as P hiding (_,_)

infixr 1 _⟶_
_⟶_ : (A B : ℕ → Set) → (ℕ → Set)
(A ⟶ B) n = A n → B n

infixr 2 _⊕_
_⊕_ : (A B : ℕ → Set) → (ℕ → Set)
(A ⊕ B) n = A n ⊎ B n

infixr 3 _⊗_
_⊗_ : (A B : ℕ → Set) → (ℕ → Set)
(A ⊗ B) n = A n × B n

infix 4 □_
□_ : (A : ℕ → Set) → (ℕ → Set)
(□ A) n = ∀ m → .(m < n) → A m

infix 5 [_]
[_] : (A : ℕ → Set) → Set
[ A ] = ∀ {n} → A n

□map : {A B : ℕ → Set} → [ A ⟶ B ] → [ □ A ⟶ □ B ]
□map f □A m m≤n = f (□A m m≤n)

open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Bool
open import Data.Maybe as M
open import Data.Char
open import Data.Nat.Properties
open import Data.List as List hiding ([_])
import Data.DifferenceList as DList
open import Data.List.NonEmpty as NonEmpty using (List⁺ ; _∷⁺_ ; _∷_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable

∣_∣≡_ : {A : Set} → List A → ℕ → Set
∣ []     ∣≡ zero  = ⊤
∣ x ∷ xs ∣≡ suc n = ∣ xs ∣≡ n
∣ []     ∣≡ suc n = ⊥
∣ x ∷ xs ∣≡ zero  = ⊥

trivial : {A : Set} (xs : List A) → ∣ xs ∣≡ length xs
trivial []       = tt
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

extract : {A : ℕ → Set} → [ □ A ] → [ A ]
extract a {n} = a {suc n} n ≤-refl

String = Vec Char

<⇒≤ : ∀ {m n} → m < n → m ≤ n
<⇒≤ = ≤-trans (n≤1+n _)

record Success (Tok : Set) (A : Set) (n : ℕ) : Set where
  constructor _,_,_,_
  field
    value : A
    size  : ℕ
    small : size < n
    left  : Vec Tok size

record Parser (Tok : Set) (A : Set) (n : ℕ) : Set where
  constructor mkParser
  field runParser : ∀ {m} → .(m ≤ n) → Vec Tok m → Maybe (Success Tok A m)
open Parser

open import Function

module _ {Tok A B : Set} where

 smap : (A → B) → [ Success Tok A ⟶ Success Tok B ]
 smap f (a , n , n<m , s) = f a , n , n<m , s

 infixr 5 _<$>_
 _<$>_ : (A → B) → [ Parser Tok A ⟶ Parser Tok B ]
 runParser (f <$> p) lt s = M.map (smap f) (runParser p lt s)

 infixr 5 _<$_
 _<$_ : B → [ Parser Tok A ⟶ Parser Tok B ]
 b <$ p = const b <$> p

return : {Tok A : Set} → [ Parser Tok A ⟶ □ Parser Tok A ]
runParser (return p lt le) s = runParser p (≤-trans s (<⇒≤ le))

module _ {A : ℕ → Set} where

 duplicate : [ □ A ⟶ □ □ A ]
 duplicate □A m m<n p p<m = □A p (<-trans p<m m<n)

 fix□ : [ □ A ⟶ A ] → [ □ A ]
 fix□ f {zero}  = λ _ ()
 fix□ f {suc n} = λ m m<sn → f (λ p p<m → fix□ f p (≤-trans p<m (≤-pred m<sn)))

fix : ∀ A → [ □ A ⟶ A ] → [ A ]
fix A = extract ∘ fix□

open import Relation.Nullary

anyChar : [ Parser Char Char ]
runParser anyChar lt s with vec s
... | nil       = nothing
... | cons a as = just (a , _ , ≤-refl , as)

char : Char → [ Parser Char Char ]
runParser (char c) lt s with vec s
... | nil       = nothing
... | cons a as with a Data.Char.≟ c
runParser (char c) lt _ | cons a as | yes p = just (c , _ , ≤-refl , as)
runParser (char c) lt _ | cons a as | no ¬p = nothing

open import Category.Monad
import Level
module MM = RawMonad (M.monad {Level.zero}) using (_>>=_)

module _ {Tok A B : Set} where

 _&>>=_ : [ Parser Tok A ⟶ (const A ⟶ □ Parser Tok B) ⟶ Parser Tok (A × B) ]
 runParser (A &>>= B) m≤n s =
   runParser A m≤n s MM.>>= λ rA →
   let (a , p , p<m , s′) = rA in
   runParser (B a p (≤-trans p<m m≤n)) ≤-refl s′ MM.>>= λ rB →
   let (b , q , q<p , s′′) = rB in
   just ((a P., b) , q , <-trans q<p p<m , s′′)

 _>>=_ : [ Parser Tok A ⟶ (const A ⟶ □ Parser Tok B) ⟶ Parser Tok B ]
 A >>= B = proj₂ <$> A &>>= B

 infixl 4 _<&>_ _<&_ _&>_
 _<&>_ : [ Parser Tok A ⟶ □ Parser Tok B ⟶ Parser Tok (A × B) ]
 A <&> B = A &>>= const B

 _<&_ : [ Parser Tok A ⟶ □ Parser Tok B ⟶ Parser Tok A ]
 A <& B = proj₁ <$> (A <&> B)

 _&>_ : [ Parser Tok A ⟶ □ Parser Tok B ⟶ Parser Tok B ]
 A &> B = proj₂ <$> (A <&> B)

module _ {Tok A B : Set} where

 infixr 5 _<*>_
 _<*>_ : [ Parser Tok (A → B) ⟶ Parser Tok A ⟶ Parser Tok B ]
 F <*> A = uncurry _$_ <$> (F <&> return A)

 infixr 3 _<⊎>_
 _<⊎>_ : [ Parser Tok A ⟶ Parser Tok B ⟶ Parser Tok (A ⊎ B) ]
 runParser (A <⊎> B) m≤n s with runParser (inj₁ <$> A) m≤n s
 ... | nothing = runParser (inj₂ <$> B) m≤n s
 ... | r = r

 hchainl : [ Parser Tok A ⟶ □ Parser Tok (A → B → A) ⟶ □ Parser Tok B ⟶ Parser Tok A ]
 runParser (hchainl {m} pA pOp pB) {n} n≤m = kickstart where

   goal : ℕ → Set
   goal = Success Tok A

   step : ∀ {n p} (p≤n : p ≤ n)
          (r : (□ (_≤ n ⟶ goal ⟶ goal)) p) (acc : goal p) →
          Success Tok ((A → B → A) × B) (Success.size acc) → goal p
   step p≤n rec (a , q , q<p , _) ((op P., b) , r , r<q , str) =
     let q≤n = ≤-trans (<⇒≤ q<p) p≤n
         (a , s , s<q , str′) = rec q q<p q≤n (op a b , r , r<q , str) in
     a , s , <-trans s<q q<p , str′

   chain : goal n → goal n
   chain = (fix (_≤ n ⟶ goal ⟶ goal) $ λ {p} rec p≤n acc →
           let (a , q , q<p , s) = acc
               .q<m : q < m
               q<m = ≤-trans q<p (≤-trans p≤n n≤m)
           in maybe (step p≤n rec acc) acc $ runParser
              (pOp q q<m <&> return (pB q q<m)) ≤-refl s)
           ≤-refl

   kickstart : Vec Tok n → Maybe (goal n)
   kickstart s = runParser pA n≤m s MM.>>= just ∘ chain

module _ {Tok A : Set} where

 guard : (A → Bool) → [ Parser Tok A ⟶ Parser Tok A ]
 runParser (guard p A) m≤n s =
   runParser A m≤n s MM.>>= λ a →
   if p (Success.value a) then just a else nothing

 infixr 3 _<|>_
 _<|>_ : [ Parser Tok A ⟶ Parser Tok A ⟶ Parser Tok A ]
 A₁ <|> A₂ = [ id , id ]′ <$> (A₁ <⊎> A₂)

 chainl1 : [ Parser Tok A ⟶ □ Parser Tok (A → A → A) ⟶ Parser Tok A ]
 chainl1 a op = hchainl a op (return a)

 head+tail : [ Parser Tok A ⟶ □ Parser Tok A ⟶ Parser Tok (List⁺ A) ]
 runParser (head+tail {m} pHd pTl) {n} n≤m = kickstart where

   goal : ℕ → Set
   goal = Success Tok (List⁺ A)

   step : ∀ {n p} (p≤n : p ≤ n) (r : (□ (_≤ n ⟶ goal ⟶ goal)) p)
          (acc : goal p) → Success Tok A (Success.size acc) → goal p
   step p≤n rec (a , q , q<p , _) (b , r , r<q , str) =
     let q≤n = ≤-trans (<⇒≤ q<p) p≤n
         (a , s , s<q , str′) = rec q q<p q≤n ((b ∷⁺ a) , r , r<q , str) in
     a , s , <-trans s<q q<p , str′

   chain : goal n → goal n
   chain = (fix (_≤ n ⟶ goal ⟶ goal) $ λ {p} rec p≤n acc →
           let (a , q , q<p , s) = acc
               .q<m : q < m
               q<m = ≤-trans q<p (≤-trans p≤n n≤m)
           in maybe (step p≤n rec acc) acc $ runParser (pTl q q<m) ≤-refl s)
           ≤-refl

   kickstart : Vec Tok n → Maybe (goal n)
   kickstart s = runParser pHd n≤m s MM.>>=
                 just ∘ smap NonEmpty.reverse ∘ chain ∘ smap (_∷ [])

 list⁺ : [ Parser Tok A ⟶ Parser Tok (List⁺ A) ]
 list⁺ pA = head+tail pA (return pA)

parens : {A : Set} → [ □ Parser Char A ⟶ Parser Char A ]
parens A = char '(' &> A <& return (char ')')

---------------------------------------------------------------
-- EXAMPLES
---------------------------------------------------------------

import Data.String as String
open String using () renaming (String to Text)

`_ : (s : Text) → String (length (String.primStringToList s))
` s = let xs = String.primStringToList s in mkVec xs (trivial xs)

infix 0 _!
data Singleton {A : Set} : A → Set where
  _! : (a : A) → Singleton a

_∈_ : {A : Set} → Text → [ Parser Char A ] → Set
s ∈ A with runParser A (n≤1+n _) (` s)
s ∈ A | just (a , 0 , _ , _)  = Singleton a
s ∈ A | _ = ⊥

Nat : [ Parser Char ℕ ]
Nat = fix _ (λ r → [ id , suc ]′ <$> (0 <$ char 'Z' <⊎> char 'S' &> r))

_ : "Z" ∈ Nat
_ = 0 !

_ : "SSSSSZ" ∈ Nat
_ = 5 !

List′ : {A : Set} → [ Parser Char A ] → [ Parser Char (List A) ]
List′ A = fix _ (λ r → [ id , uncurry _∷_ ]′
                      <$> ([] <$ char 'N'
                      <⊎> char 'C' &> return A <&> r))

_ : "CSSSZCSSZCZN" ∈ List′ Nat
_ = 3 ∷ 2 ∷ 0 ∷ [] !

data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

BTree : {A : Set} → [ Parser Char A ] → [ Parser Char (Tree A) ]
BTree A = fix _ (λ r → [ leaf , uncurry node ]′
                      <$> (char 'L' &> return A
                      <⊎> char 'N' &> r <&> r))

_ : "NNLZLSSZLZ" ∈ BTree Nat
_ = node (node (leaf 0) (leaf 2)) (leaf 0) !

_ : "NNLZLSSZNLZLSSSZ" ∈ BTree Nat
_ = node (node (leaf 0) (leaf 2)) (node (leaf 0) (leaf 3)) !

_ : "NLNLZLZLLSZ" ∈ BTree (BTree Nat)
_ = node (leaf (node (leaf 0) (leaf 0))) (leaf (leaf 1)) !

alpha : [ Parser Char Char ]
alpha = guard (λ c → any (c ==_) alphas) anyChar where

  alphas = String.toList "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

digit : [ Parser Char ℕ ]
digit = 0 <$ char '0'
    <|> 1 <$ char '1'
    <|> 2 <$ char '2'
    <|> 3 <$ char '3'
    <|> 4 <$ char '4'
    <|> 5 <$ char '5'
    <|> 6 <$ char '6'
    <|> 7 <$ char '7'
    <|> 8 <$ char '8'
    <|> 9 <$ char '9'

decimal : [ Parser Char ℕ ]
decimal = proj₁ ∘ foldr (λ v → uncurry $ λ t d → t + v * d P., 10 * d) (0 P., 1)
        ∘ NonEmpty.toList <$> list⁺ digit

_ : "1005" ∈ decimal
_ = 1005 !

-- Example taken from parsec's documentation
-- https://hackage.haskell.org/package/parsec-3.1.11/docs/Text-Parsec-Combinator.html#v:chainl1

data Expr : Set where
  Var     : Char → Expr
  Lit     : ℕ → Expr
  Add Sub : Expr → Expr → Expr
  Mul Div : Expr → Expr → Expr

Expr′ : [ Parser Char Expr ]
Expr′ = fix (Parser Char Expr) $ λ rec →
        let var    = Var <$> alpha
            lit    = Lit <$> decimal
            addop  = Add <$ char '+' <|> Sub <$ char '-'
            mulop  = Mul <$ char '*' <|> Div <$ char '/'
            factor = parens rec <|> var <|> lit
            term   = chainl1 factor $ return mulop
            expr   = chainl1 term   $ return addop
        in expr

_ : "x+y+z" ∈ Expr′
_ = Add (Add (Var 'x') (Var 'y')) (Var 'z') !

_ : "x+y*z+t" ∈ Expr′
_ = Add (Add (Var 'x') (Mul (Var 'y') (Var 'z'))) (Var 't') !

_ : "(x+y)*z*t+u" ∈ Expr′
_ = Add (Mul (Mul (Add (Var 'x') (Var 'y')) (Var 'z')) (Var 't')) (Var 'u') !

_ : "10*(x+5*y)+z*7" ∈ Expr′
_ = Add (Mul (Lit 10) (Add (Var 'x') (Mul (Lit 5) (Var 'y')))) (Mul (Var 'z') (Lit 7)) !

-- Challenge taken from stackoverflow:
-- http://stackoverflow.com/questions/12380239/agda-parsing-nested-lists

NList : Set → ℕ → Set
NList A zero    = A
NList A (suc n) = List (NList A n)

NList′ : {A : Set} → [ Parser Char A ] →
         (n : ℕ)   → [ Parser Char (NList A n) ]
NList′ A zero    = A
NList′ A (suc n) = parens $ return $ DList.toList <$>
                   chainl1 (DList.[_] <$> NList′ A n) (return $ DList._++_ <$ char ',')

_ : "((1,2,3),(4,5,6))" ∈ NList′ decimal 2
_ = (1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ [] !

_ : "((1,2,3),(4,5,6),(7,8,9,10))" ∈ NList′ decimal 2
_ = (1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ (7 ∷ 8 ∷ 9 ∷ 10 ∷ []) ∷ [] !

_ : "((1),(2))" ∈ NList′ decimal 2
_ = (1 ∷ []) ∷ (2 ∷ []) ∷ [] !

_ : "((1,2))" ∈ NList′ decimal 2
_ = (1 ∷ 2 ∷ []) ∷ [] !

_ : "(((1,2),(3,4)),((5,6),(7,8)))" ∈ NList′ decimal 3
_ = ((1 ∷ 2 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ []) ∷
    ((5 ∷ 6 ∷ []) ∷ (7 ∷ 8 ∷ []) ∷ []) ∷ [] !
