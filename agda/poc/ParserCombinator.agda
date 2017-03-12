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
open import Data.List as List hiding ([_] ; any)
import Data.DifferenceList as DList
open import Data.List.NonEmpty as NonEmpty using (List⁺ ; _∷⁺_ ; _∷_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable

∣_∣≡_ : {A : Set} → List A → ℕ → Set
∣ []     ∣≡ zero  = ⊤
∣ x ∷ xs ∣≡ suc n = ∣ xs ∣≡ n
∣ []     ∣≡ suc n = ⊥
∣ x ∷ xs ∣≡ zero  = ⊥

record Vec (A : Set) (n : ℕ) : Set where
  constructor mkVec
  field elements : List A
        .prf     : ∣ elements ∣≡ n
open Vec

data View (A : Set) : (n : ℕ) → Vec A n → Set where
  []  : View A 0 (mkVec [] _)
  _∷_ : ∀ {n} a (as : Vec A n) .{e} → View A (suc n) (mkVec (a ∷ elements as) e)

module _ {A : Set} where

 trivial : (xs : List A) → ∣ xs ∣≡ length xs
 trivial []       = tt
 trivial (x ∷ xs) = trivial xs

 fromList : (xs : List A) → Vec A (length xs)
 fromList xs = mkVec xs (trivial xs)

 vec : ∀ {n} (xs : Vec A n) → View A n xs
 vec {zero}  (mkVec [] _) = []
 vec {suc n} (mkVec (x ∷ xs) prf) = x ∷ mkVec xs prf
 vec {zero}  (mkVec (_ ∷ _) ())
 vec {suc n} (mkVec [] ())

module _ {A B : Set} where

 ∣mapfxs∣≡∣xs∣ : (f : A → B) (xs : List A) → [ ∣ xs ∣≡_ ⟶ ∣ List.map f xs ∣≡_ ]
 ∣mapfxs∣≡∣xs∣ f []       {zero}  prf = tt
 ∣mapfxs∣≡∣xs∣ f (x ∷ xs) {suc n} prf = ∣mapfxs∣≡∣xs∣ f xs prf
 ∣mapfxs∣≡∣xs∣ f []       {suc n} ()
 ∣mapfxs∣≡∣xs∣ f (x ∷ xs) {zero}  ()

 vmap : (A → B) → [ Vec A ⟶ Vec B ]
 vmap f (mkVec xs prf) = mkVec (List.map f xs) (∣mapfxs∣≡∣xs∣ f xs prf)

String = Vec Char

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

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s le₁) (s≤s le₂) = s≤s (≤-trans le₁ le₂)

<⇒≤ : ∀ {m n} → m < n → m ≤ n
<⇒≤ = ≤-trans (n≤1+n _)

module _ {A : ℕ → Set} where

 extract : [ □ A ] → [ A ]
 extract a {n} = a {suc n} n ≤-refl

 duplicate : [ □ A ⟶ □ □ A ]
 duplicate □A m m<n p p<m = □A p (<-trans p<m m<n)

 fix□ : [ □ A ⟶ A ] → [ □ A ]
 fix□ f {zero}  = λ _ ()
 fix□ f {suc n} = λ m m<sn → f (λ p p<m → fix□ f p (≤-trans p<m (≤-pred m<sn)))

module _ {A B : ℕ → Set} where

 lift2 : {C : ℕ → Set} → [ A ⟶ B ⟶ C ] → [ □ A ⟶ □ B ⟶ □ C ]
 lift2 f □A □B m m<n = f (□A m m<n) (□B m m<n)

 app : [ □ (A ⟶ B) ⟶ (□ A ⟶ □ B) ]
 app F A m m<n = F m m<n (A m m<n)

fix : ∀ A → [ □ A ⟶ A ] → [ A ]
fix A = extract ∘ fix□

module _ {A : ℕ → Set} where

 loeb : [ □ (□ A ⟶ A) ⟶ □ A ]
 loeb = fix (□ (□ A ⟶ A) ⟶ □ A) $ λ rec f m m<n →
        f m m<n (rec m m<n (duplicate f m m<n))

open import Relation.Nullary
open import Relation.Binary

open import Category.Monad
import Level
module MM = RawMonad (M.monad {Level.zero}) using (_>>=_)

module _ {Tok A : Set} where

 return : [ Parser Tok A ⟶ □ Parser Tok A ]
 runParser (return p lt le) s = runParser p (≤-trans s (<⇒≤ le))

 guard : (A → Bool) → [ Parser Tok A ⟶ Parser Tok A ]
 runParser (guard p A) m≤n s =
   runParser A m≤n s MM.>>= λ a →
   if p (Success.value a) then just a else nothing

 fail : [ Parser Tok A ]
 runParser fail = λ _ _ → nothing

module _ {Tok : Set} where

 anyTok : [ Parser Tok Tok ]
 runParser anyTok lt s with vec s
 ... | []     = nothing
 ... | a ∷ as = just (a , _ , ≤-refl , as)

module _ {Tok A B : Set} where

 _&?>>=_ : [ Parser Tok A ⟶ (const A ⟶ □ Parser Tok B) ⟶ Parser Tok (A × Maybe B) ]
 runParser (A &?>>= B) m≤n s =
   runParser A m≤n s MM.>>= λ rA →
   let (a , p , p<m , s′) = rA in
   case runParser (B a p (≤-trans p<m m≤n)) ≤-refl s′ of λ where
     nothing   → just ((a P., nothing) , p , p<m , s′)
     (just rB) → let (b , q , q<p , s′′) = rB in
                 just ((a P., just b) , q , <-trans q<p p<m , s′′)

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

 infixl 4 _<&?>_ _<&?_ _&?>_
 _<&?>_ : [ Parser Tok A ⟶ □ Parser Tok B ⟶ Parser Tok (A × Maybe B) ]
 A <&?> B = A &?>>= const B

 _<&?_ : [ Parser Tok A ⟶ □ Parser Tok B ⟶ Parser Tok A ]
 A <&? B = proj₁ <$> (A <&?> B)

 _&?>_ : [ Parser Tok A ⟶ □ Parser Tok B ⟶ Parser Tok (Maybe B) ]
 A &?> B = proj₂ <$> (A <&?> B)

 infixl 4 _<?&>_ _<?&_ _?&>_
 _<?&>_ : [ Parser Tok A ⟶ Parser Tok B ⟶ Parser Tok (Maybe A × B) ]
 runParser (A <?&> B) m≤n s with runParser A m≤n s
 ... | nothing = runParser ((λ b → nothing P., b) <$> B) m≤n s
 ... | just (a , p , p<m , s′) with runParser B (≤-trans (<⇒≤ p<m) m≤n) s′
 ... | nothing = nothing
 ... | just (b , q , q<p , s′′) = just ((just a P., b) , q , <-trans q<p p<m , s′′)

 _<?&_ : [ Parser Tok A ⟶ Parser Tok B ⟶ Parser Tok (Maybe A) ]
 A <?& B = proj₁ <$> (A <?&> B)

 _?&>_ : [ Parser Tok A ⟶ Parser Tok B ⟶ Parser Tok B ]
 A ?&> B = proj₂ <$> (A <?&> B)

module _ {Tok A B C : Set} where

 between : [ Parser Tok A ⟶ □ Parser Tok C ⟶ □ Parser Tok B ⟶ Parser Tok B ]
 between A C B = A &> B <& C

module _ {Tok : Set} {{eq? : Decidable {A = Tok} _≡_}} where

 anyOf : List Tok → [ Parser Tok Tok ]
 anyOf ts = guard (λ c → not (null ts) ∧ List.any (⌊_⌋ ∘ eq? c) ts) anyTok

 exact : Tok → [ Parser Tok Tok ]
 exact = anyOf ∘ List.[_]

 exacts : List⁺ Tok → [ Parser Tok (List⁺ Tok) ]
 exacts (x ∷ xs) = go x xs where

   go : Tok → List Tok → [ Parser Tok (List⁺ Tok) ]
   go x []       = NonEmpty.[_] <$> exact x
   go x (y ∷ xs) = uncurry _∷⁺_ <$> (exact x <&> return (go y xs))

instance eqChar = Data.Char._≟_

char : Char → [ Parser Char Char ]
char = exact

space : [ Parser Char Char ]
space = anyOf (' ' ∷ '\t' ∷ '\n' ∷ [])

import Data.String as String
open String using () renaming (String to Text)

text : (t : Text) {_ : T (not $ null $ String.toList t)} → [ Parser Char Text ]
text t {pr} with String.toList t | pr
... | []     | ()
... | x ∷ xs | _ = String.fromList ∘ NonEmpty.toList <$> exacts (x ∷ xs)

parens : {A : Set} → [ □ Parser Char A ⟶ Parser Char A ]
parens = between (char '(') (return (char ')'))

module _ {Tok A B : Set} where

 infixr 5 _<*>_
 _<*>_ : [ Parser Tok (A → B) ⟶ Parser Tok A ⟶ Parser Tok B ]
 F <*> A = uncurry _$_ <$> (F <&> return A)

 infixr 3 _<⊎>_
 _<⊎>_ : [ Parser Tok A ⟶ Parser Tok B ⟶ Parser Tok (A ⊎ B) ]
 runParser (A <⊎> B) m≤n s with runParser (inj₁ <$> A) m≤n s
 ... | nothing = runParser (inj₂ <$> B) m≤n s
 ... | r = r

module _ {Tok A : Set} where

 infixr 3 _<|>_
 _<|>_ : [ Parser Tok A ⟶ Parser Tok A ⟶ Parser Tok A ]
 A₁ <|> A₂ = [ id , id ]′ <$> (A₁ <⊎> A₂)

 schainl : [ Success Tok A ⟶ □ Parser Tok (A → A) ⟶ Success Tok A ]
 schainl =
   fix (Success Tok A ⟶ □ Parser Tok (A → A) ⟶ Success Tok A) $ λ rec sA op →
   let (a , p , p<m , s) = sA
       rec′ = duplicate op p p<m
   in case runParser (op p p<m) ≤-refl s of λ where
        nothing    → sA
        (just sOp) →
          let (f , q , q<p , s′)    = sOp
              (res , r , r<p , s′′) = rec p p<m (f a , q , q<p , s′) rec′
          in res , r , <-trans r<p p<m , s′′

 iterate : [ Parser Tok A ⟶ □ Parser Tok (A → A) ⟶ Parser Tok A ]
 runParser (iterate {n} a op) m≤n s =
   runParser a m≤n s MM.>>= λ sA →
   just $ schainl sA $ λ p p<m → op p (≤-trans p<m m≤n)

module _ {Tok A B : Set} where

 hchainl : [ Parser Tok A ⟶ □ Parser Tok (A → B → A) ⟶ □ Parser Tok B ⟶ Parser Tok A ]
 hchainl A op B = iterate A (lift2 (_<*>_ ∘ (flip <$>_)) op B)

module _ {Tok A : Set} where

 chainr1 : [ Parser Tok A ⟶ □ Parser Tok (A → A → A) ⟶ Parser Tok A ]
 chainr1 =
   fix (Parser Tok A ⟶ □ Parser Tok (A → A → A) ⟶ Parser Tok A) $ λ {n} rec A op →
     mkParser $ λ m≤n s →
     runParser A m≤n s MM.>>= λ rA →
     let (a , p , p<m , s′) = rA
         .p<n : p < n
         p<n = ≤-trans p<m m≤n
     in case runParser (op p p<n) ≤-refl s′ of λ where
        nothing   → just rA
        (just (f , q , q<p , s′′)) →
          let .q<n : q < n
              q<n = <-trans q<p p<n
          in case runParser (rec q q<n (return A q q<n) (duplicate op q q<n)) ≤-refl s′′
             of λ where
          nothing                     → just rA
          (just (b , r , r<q , s′′′)) →
             just (f a b , r , <-trans r<q (<-trans q<p p<m) , s′′′)

 chainl1 : [ Parser Tok A ⟶ □ Parser Tok (A → A → A) ⟶ Parser Tok A ]
 chainl1 a op = hchainl a op (return a)

 head+tail : [ Parser Tok A ⟶ □ Parser Tok A ⟶ Parser Tok (List⁺ A) ]
 head+tail hd tl = NonEmpty.reverse
               <$> (iterate (NonEmpty.[_] <$> hd) (□map (NonEmpty._∷⁺_ <$>_) tl))

 list⁺ : [ Parser Tok A ⟶ Parser Tok (List⁺ A) ]
 list⁺ pA = head+tail pA (return pA)

spaces : [ Parser Char (List⁺ Char) ]
spaces = list⁺ space

module _ {A : Set} where

  withSpaces : [ Parser Char A ⟶ Parser Char A ]
  withSpaces A = spaces ?&> A <&? return spaces

---------------------------------------------------------------
-- EXAMPLES
---------------------------------------------------------------

`_ : (s : Text) → String (length (String.toList s))
` s = let xs = String.toList s in mkVec xs (trivial xs)

infix 0 _!
data Singleton {A : Set} : A → Set where
  _! : (a : A) → Singleton a

record Tokenizer (A : Set) : Set where
  constructor mkTokenizer
  field tokenize : List Char → List A

  fromText : Text → List A
  fromText = tokenize ∘ String.toList

instance tokChar = mkTokenizer id

_∈_ : {Tok A : Set} {{t : Tokenizer Tok}} → Text → [ Parser Tok A ] → Set
_∈_ {{t}} s A with runParser A (n≤1+n _) (fromList $ Tokenizer.fromText t s)
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
alpha = anyOf $ String.toList "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"

record Identifier : Set where
  constructor mkIdentifier
  field getIdentifier : List⁺ Char

identifier : [ Parser Char Identifier ]
identifier = mkIdentifier <$> list⁺ alpha

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
            addop  = withSpaces (Add <$ char '+' <|> Sub <$ char '-')
            mulop  = withSpaces (Mul <$ char '*' <|> Div <$ char '/')
            factor = parens rec <|> var <|> lit
            term   = chainl1 factor $ return mulop
            expr   = chainl1 term   $ return addop
        in expr

_ : "x+y+z" ∈ Expr′
_ = Add (Add (Var 'x') (Var 'y')) (Var 'z') !

_ : "x + y + z" ∈ Expr′
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

-- Well-parenthesised string
data PAR : Set where
  LPAR RPAR : PAR
  LCUR RCUR : PAR
  LSQU RSQU : PAR

instance
  {- eqPAR x y             -}
  {- C-c C-c x y           -}
  {- F3 C-c C-f C-c C-a F4 -}
  {- F4 (repeat ∣PAR∣^2)    -}
  eqPAR : Decidable {A = PAR} _≡_
  eqPAR LPAR LPAR = yes refl
  eqPAR LPAR RPAR = no (λ ())
  eqPAR LPAR LCUR = no (λ ())
  eqPAR LPAR RCUR = no (λ ())
  eqPAR LPAR LSQU = no (λ ())
  eqPAR LPAR RSQU = no (λ ())
  eqPAR RPAR LPAR = no (λ ())
  eqPAR RPAR RPAR = yes refl
  eqPAR RPAR LCUR = no (λ ())
  eqPAR RPAR RCUR = no (λ ())
  eqPAR RPAR LSQU = no (λ ())
  eqPAR RPAR RSQU = no (λ ())
  eqPAR LCUR LPAR = no (λ ())
  eqPAR LCUR RPAR = no (λ ())
  eqPAR LCUR LCUR = yes refl
  eqPAR LCUR RCUR = no (λ ())
  eqPAR LCUR LSQU = no (λ ())
  eqPAR LCUR RSQU = no (λ ())
  eqPAR RCUR LPAR = no (λ ())
  eqPAR RCUR RPAR = no (λ ())
  eqPAR RCUR LCUR = no (λ ())
  eqPAR RCUR RCUR = yes refl
  eqPAR RCUR LSQU = no (λ ())
  eqPAR RCUR RSQU = no (λ ())
  eqPAR LSQU LPAR = no (λ ())
  eqPAR LSQU RPAR = no (λ ())
  eqPAR LSQU LCUR = no (λ ())
  eqPAR LSQU RCUR = no (λ ())
  eqPAR LSQU LSQU = yes refl
  eqPAR LSQU RSQU = no (λ ())
  eqPAR RSQU LPAR = no (λ ())
  eqPAR RSQU RPAR = no (λ ())
  eqPAR RSQU LCUR = no (λ ())
  eqPAR RSQU RCUR = no (λ ())
  eqPAR RSQU LSQU = no (λ ())
  eqPAR RSQU RSQU = yes refl

  tokPAR : Tokenizer PAR
  tokPAR = mkTokenizer $ List.foldr (_++_ ∘ toPAR) [] where

    toPAR : Char → List PAR
    toPAR c = if c == '(' then LPAR ∷ []
         else if c == ')' then RPAR ∷ []
         else if c == '{' then LCUR ∷ []
         else if c == '}' then RCUR ∷ []
         else if c == '[' then LSQU ∷ []
         else if c == ']' then RSQU ∷ []
         else [] -- ignoring other characters as noise

PAR′ : [ Parser PAR ⊤ ]
PAR′ = fix (Parser PAR _) $ λ rec →
        tt <$ ((exact LPAR <&?> rec) <& return (exact RPAR <&?> rec))
    <|> tt <$ ((exact LCUR <&?> rec) <& return (exact RCUR <&?> rec))
    <|> tt <$ ((exact LSQU <&?> rec) <& return (exact RSQU <&?> rec))


_ : "hel[{(lo({((wor))ld})wan)t}som{e()[n]o}i(s)e]?" ∈ PAR′
_ = _ !

data Type : Set where
  `κ   : ℕ → Type
  _`→_ : Type → Type → Type

Type′ : [ Parser Char Type ]
Type′ = fix _ $ λ rec → chainr1 (`κ <$> decimal <|> parens rec)
                                (return $ _`→_ <$ withSpaces (char '→'))

_ : "1 → (2 → 3) → 4" ∈ Type′
_ = `κ 1 `→ ((`κ 2 `→ `κ 3) `→ `κ 4) !

mutual

  data Val : Set where
    Lam : Identifier → Val → Val
    Emb : Neu → Val

  data Neu : Set where
    Var : Identifier → Neu
    Cut : Val → Type → Neu
    App : Neu → Val → Neu

Val′ : [ Parser Char Val ]
Val′ = fix _ $ λ rec →
       let var = Var <$> identifier
           cut = uncurry Cut <$> (char '(' &> rec
                             <& return (withSpaces (char ':'))
                             <&> return Type′
                             <& return (char ')'))
           neu = hchainl (var <|> cut) (return (App <$ space)) rec
       in uncurry Lam <$> (char 'λ' &> return (withSpaces identifier)
                                   <&> return ((char '.')
                                    &> rec))
          <|> Emb <$> neu

_ : "λx.x" ∈ Val′
_ = Lam (mkIdentifier ('x' ∷ []))
        (Emb (Var (mkIdentifier ('x' ∷ [])))) !

_ : "λx.λy.x y" ∈ Val′
_ = Lam (mkIdentifier ('x' ∷ []))
   (Lam (mkIdentifier ('y' ∷ []))
   (Emb (App (Var (mkIdentifier ('x' ∷ [])))
             (Emb (Var (mkIdentifier ('y' ∷ []))))))) !

_ : "λx.(λx.x : 1 → 1) x" ∈ Val′
_ = Lam (mkIdentifier ('x' ∷ []))
    (Emb (App
              (Cut (Lam (mkIdentifier ('x' ∷ []))
                        (Emb (Var (mkIdentifier ('x' ∷ [])))))
                   (`κ 1 `→ `κ 1))
              (Emb (Var (mkIdentifier ('x' ∷ [])))))) !
