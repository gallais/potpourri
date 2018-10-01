-- The content of this file is based on Edwin Brady's
-- Resource-dependent Algebraic Effects

module papers.depeff14.Effect where

open import Size
open import Codata.Thunk

open import Data.Unit
open import Data.Bool
open import Data.Char
open import Data.Char.Unsafe renaming (_≟_ to _≟C_)
open import Data.List as List
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Show as NatShow
open import Data.String as String
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary
open import Data.List.Membership.DecPropositional _≟C_ using (_∈?_)

---------------------------------------------------------------------------
-- Effects

Effect : Set₂
Effect = (A : Set) (I : Set) (O : A → Set) → Set₁

record EFFECT : Set₂ where
  constructor MkEFFECT
  field parameter : Set
        effect    : Effect

data Eff (i : Size) (A : Set) (Pre : List EFFECT) : (Post : A → List EFFECT) → Set₂ where
  Call : ∀ {E I O} (pr : MkEFFECT I E ∈ Pre) → E A I O →
         Eff i A Pre (λ a → pr ∷= MkEFFECT (O a) E)
  Pure : A → Eff i A Pre (λ _ → Pre)
  Bind : ∀ {B Post₁ Post₂} →
         Thunk (λ i → Eff i B Pre Post₁) i →
         ((b : B) → Thunk (λ i → Eff i A (Post₁ b) Post₂) i) →
         Eff i A Pre Post₂

_>>=_ : ∀ {A B Pre Post₁ Post₂} →
        Eff ∞ A Pre Post₁ → (∀ a → Eff ∞ B (Post₁ a) Post₂) →
        Eff ∞ B Pre Post₂
m >>= f = Bind (λ where .force → m) λ where a .force → f a

_>>_ : ∀ {A B Pre Post₁ Post₂} →
       Eff ∞ A Pre Post₁ → (∀ {a} → Eff ∞ B (Post₁ a) Post₂) →
       Eff ∞ B Pre Post₂
m >> n = m >>= λ _ → n


Eff' : Size → Set → List EFFECT → List EFFECT → Set₂
Eff' i A Pre Post = Eff i A Pre (λ _ → Post)

Eff′ : Size → Set → List EFFECT → Set₂
Eff′ i A Pre = Eff' i A Pre Pre

---------------------------------------------------------------------------
-- Handlers

record Handler (E : Effect) (M : Set → Set) : Set₁ where
  field handle : ∀ {A I O R} → I → E A I O →
                 (∀ a → O a → M R) → M R
open Handler public

---------------------------------------------------------------------------
-- Examples

-- State

data State : Effect where
  Get : ∀ {A}       → State A A (λ _ → A)
  Put : ∀ {A B} → B → State ⊤ A (λ _ → B)

STATE : Set → EFFECT
STATE T = MkEFFECT T State

hState : ∀ M → Handler State M
handle (hState M) i Get     k = k i i
handle (hState M) i (Put v) k = k _ v

get : ∀ {S} → Eff′ ∞ S [ STATE S ]
get = Call (here refl) Get

put : ∀ {S} → S → Eff′ ∞ ⊤ [ STATE S ]
put s = Call (here refl) (Put s)

putM : ∀ {S T} → T → Eff' ∞ ⊤ [ STATE S ] [ STATE T ]
putM t = Call (here refl) (Put t)

-- STD IO

data StdIO : Effect where
  PutStrLn : String → StdIO ⊤ ⊤ (λ _ → ⊤)

STDIO : EFFECT
STDIO = MkEFFECT ⊤ StdIO

putStrLn : String → Eff′ ∞ ⊤ [ STDIO ]
putStrLn str = Call (here refl) (PutStrLn str)

-- File I/O

data Mode : Set where
  Read Write : Mode

record OpenFile (m : Mode) : Set where
  constructor MkOpenFile
  field filepath : String

data FileIO : Effect where
  Open     : String → (m : Mode) →
             FileIO Bool ⊤ $ λ ok → if ok then OpenFile m else ⊤
  Close    : ∀ {m} → FileIO ⊤ (OpenFile m) (λ _ → ⊤)
  ReadLine : FileIO String (OpenFile Read) (λ _ → OpenFile Read)
  Writeine : String → FileIO ⊤ (OpenFile Write) (λ _ → OpenFile Write)
  EOF      : FileIO Bool (OpenFile Read) (λ _ → OpenFile Read)

FILEIO : Set → EFFECT
FILEIO A = MkEFFECT A FileIO

fopen : String → (m : Mode) →
        Eff ∞ Bool [ FILEIO ⊤ ] $ λ ok →
                   [ FILEIO (if ok then OpenFile m else ⊤) ]
fopen f m = Call (here refl) (Open f m) -- mising Call p8 of the paper

fclose : ∀ {m} → Eff' ∞ ⊤ [ FILEIO (OpenFile m) ] [ FILEIO ⊤ ]
fclose = Call (here refl) Close

readLine : Eff′ ∞ String [ FILEIO (OpenFile Read) ]
readLine = Call (here refl) ReadLine

readFile : ∀ {i} → Eff′ i (List String) [ FILEIO (OpenFile Read) ]
readFile = Bind (λ where .force → Call (here refl) EOF) $ λ where
  true  .force → Pure []
  false .force → Bind (λ where .force → readLine) $ λ where
    str .force → Bind (λ where .force → readFile) $ λ where
      strs .force → Pure (str ∷ strs)

dumpFile : String → Eff′ ∞ (Maybe (List String)) [ FILEIO ⊤ ]
dumpFile name = do
  true ← fopen name Read where false → Pure nothing
  strs ← readFile
  fclose
  Pure (just strs)

-- Guessing Game

data GState : Set where
  Running    : ℕ → ℕ → GState
  NotRunning : GState

data Mystery : GState → Set where
  Init     : Mystery NotRunning
  GameWon  : String → Mystery NotRunning
  GameLost : String → Mystery NotRunning
  MkGame   : ∀ {m} → String → (g : ℕ) → (got : List Char) → Vec Char m →
             Mystery (Running g m)

import Data.AVL.Sets <-isStrictTotalOrder as S

letters : String → List Char
letters = List.boolFilter (not ∘′ isSpace)
        ∘′ List.map fromNat
        ∘′ S.toList
        ∘′ S.fromList
        ∘′ List.map toNat
        ∘′ toList

data MysteryRules : Effect where
  Guess    : ∀ {g w} → Char →
             MysteryRules Bool (Mystery (Running (suc g) (suc w))) $ λ inWord →
             if inWord then Mystery (Running (suc g) w) else Mystery (Running g (suc w))
  Won      : ∀ {g} → MysteryRules ⊤ (Mystery (Running g 0)) (λ _ → Mystery NotRunning)
  Lost     : ∀ {w} → MysteryRules ⊤ (Mystery (Running 0 w)) (λ _ → Mystery NotRunning)
  NewWord  : ∀ str → let w = List.length $ letters str in
             MysteryRules ⊤ (Mystery NotRunning) (λ _ → Mystery (Running 6 w))
  StrState : ∀ {h} → MysteryRules String (Mystery h) (λ _ → Mystery h)

initState : ∀ str → Mystery (Running 6 (List.length $ letters str))
initState str = MkGame str 6 [] (Vec.fromList (letters str))

MYSTERY : GState → EFFECT
MYSTERY h = MkEFFECT (Mystery h) MysteryRules

shrink : ∀ {a} {A : Set a} {n x} (xs : Vec A n) → x ∈ Vec.toList xs → Vec A (pred n)
shrink (x ∷ xs)     (here px) = xs
shrink (x ∷ y ∷ xs) (there v) = x ∷ shrink (y ∷ xs) v

showGState : GState → String
showGState NotRunning    = "NotRunning"
showGState (Running g w) = String.concat
  $ "Running: "
  ∷ NatShow.show g ∷ " guesses left; "
  ∷ NatShow.show w ∷ " letters missing."
  ∷ []

showMystery : ∀ {h} → Mystery h → String
showMystery Init                 = "Let's go!"
showMystery (GameWon w)          = "You won!"
showMystery (GameLost w)         = "You lost!"
showMystery {h} (MkGame _ _ _ _) = showGState h

hMystery : ∀ {m} → Handler MysteryRules m
handle hMystery (MkGame w _ _ []) Won  k = k _ (GameWon w)
handle hMystery (MkGame w 0 _ _)  Lost k = k _ (GameLost w)

handle hMystery i StrState      k = k (showMystery i) i
handle hMystery i (NewWord str) k = k _ (initState str)

handle hMystery (MkGame str _ got w) (Guess c) k = case c ∈? Vec.toList w of λ where
  (yes p) → k true (MkGame str _ (c ∷ got) (shrink w p))
  (no ¬p) → k false (MkGame str _ got w)

game : ∀ g w → Eff ∞ ⊤ [ MYSTERY (Running (suc g) w) ] (λ _ → [ MYSTERY NotRunning ])
game g zero       = Call (here refl) Won
game g w@(suc w') = do
  false ← Call (here refl) (Guess 'c') where true → game g w'
  case g return (λ g → Eff' ∞ ⊤ [ MYSTERY (Running g _) ] _) of λ where
    zero    → Call (here refl) Lost
    (suc g) → game g w

words : Vec String _
words = "idris" ∷ "agda" ∷ "haskell" ∷ "miranda" ∷ "java"
      ∷ "javascript" ∷ "fortran" ∷ "basic" ∷ "erlang" ∷ "racket" ∷ "clean"
      ∷ "links" ∷ "coffeescript" ∷ "rust" ∷ []
