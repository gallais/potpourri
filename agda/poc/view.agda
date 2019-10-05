module poc.view where

open import Data.Unit
open import Reflection hiding (return; _>>_; _>>=_)
open import Reflection.Term as Term
open import Reflection.Argument as Arg
open import Reflection.Definition
open import Reflection.Pattern
open import Reflection.Argument.Information
open import Reflection.Name as Name
open import Reflection.Abstraction

open import Data.Bool.Base
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _<ᵇ_)
import Data.Nat.Show as ℕₛ
import Data.Nat.Properties as ℕₚ
import Data.Fin.Base as Fin
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.List.Base as List using (List; []; _∷_)
import Data.List.Relation.Unary.Any as Any
open import Data.Product
open import Data.String
open import Function
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

record Raise : Set where
  constructor mkRaise
  field protected : ℕ
        offset    : ℕ

initRaise : ℕ → Raise
initRaise = mkRaise 0

wkRaise : ℕ → Raise → Raise
wkRaise n (mkRaise protected offset) = mkRaise (n + protected) (n + offset)

raiseVar : Raise → ℕ → ℕ
raiseVar r k = if k <ᵇ protected then k else offset + k
  where open Raise r

raiseSort     : Raise → Sort → Sort
raiseAbsTerm  : Raise → Abs Term → Abs Term
raiseTerm     : Raise → Term → Term
raiseArgTerm  : Raise → Arg Term → Arg Term
raiseArgTerms : Raise → List (Arg Term) → List (Arg Term)
raiseClause   : Raise → Clause → Clause
raiseClauses  : Raise → List Clause → List Clause

raiseSort r (set t) = set (raiseTerm r t)
raiseSort r (lit n) = lit n
raiseSort r unknown = unknown

raiseAbsTerm r (abs s t) = abs s (raiseTerm (wkRaise 1 r) t)

raiseTerm r (var x args)      = var (raiseVar r x) (raiseArgTerms r args)
raiseTerm r (con c args)      = con c (raiseArgTerms r args)
raiseTerm r (def f args)      = def f (raiseArgTerms r args)
raiseTerm r (lam v t)         = lam v (raiseAbsTerm r t)
raiseTerm r (pat-lam cs args) = pat-lam (raiseClauses r cs) (raiseArgTerms r args)
raiseTerm r (pi a b)          = pi (raiseArgTerm r a) (raiseAbsTerm r b)
raiseTerm r (sort s)          = sort (raiseSort r s)
raiseTerm r (lit l)           = lit l
raiseTerm r (meta id args)    = meta id (raiseArgTerms r args)
raiseTerm r unknown           = unknown

raiseArgTerm r (arg i x) = arg i (raiseTerm r x)

raiseArgTerms r []       = []
raiseArgTerms r (t ∷ ts) = raiseArgTerm r t ∷ raiseArgTerms r ts

raiseClause r (absurd-clause ps) = absurd-clause ps
raiseClause r (clause ps t)      = clause ps (raiseTerm (wkRaise count r) t)
  where
    measure  : Pattern → ℕ
    measures : List (Arg Pattern) → ℕ

    measure (con c ps) = measures ps
    measure dot        = 0
    measure (var s)    = 1
    measure (lit l)    = 0
    measure (proj f)   = 0
    measure absurd     = 0

    measures []             = 0
    measures (arg _ p ∷ ps) = measure p + measures ps

    count = measures ps


raiseClauses r []       = []
raiseClauses r (c ∷ cs) = raiseClause r c ∷ raiseClauses r cs

private

  record Absₙ (T : Set) (n : ℕ) : Set where
    constructor mkAbsₙ
    field
      names  : Vec String n
      unAbsₙ : T

  openAbs : ∀ {T n} → Abs (Absₙ T n) → Absₙ T (suc n)
  openAbs (abs x (mkAbsₙ xs t)) = mkAbsₙ (x ∷ xs) t

  unAbsₙTerm : ∀ {n} → Absₙ Term n → Term
  unAbsₙTerm {n} t = raiseTerm (initRaise n) (t .Absₙ.unAbsₙ)

  runAbsₙ : ∀ {T} → Absₙ T 0 → T
  runAbsₙ = Absₙ.unAbsₙ

  closeAbs : ∀ {T m} → Absₙ T (suc m) → Abs (Absₙ T m)
  closeAbs (mkAbsₙ (x ∷ xs) t) = abs x (mkAbsₙ xs t)

  infixl 5 _<$>_
  infixl 4 _<*>_

  _<$>_ : ∀ {S T n} → (S → T) → Absₙ S n → Absₙ T n
  f <$> (mkAbsₙ xs t) = mkAbsₙ xs (f t)

  _<*>_ : ∀ {S T n} → Absₙ (S → T) n → Absₙ S n → Absₙ T n
  (mkAbsₙ xs f) <*> (mkAbsₙ _ t) = mkAbsₙ xs (f t)

data Telescope (T : Set) : ℕ → Set where
  []   : Telescope T 0
  _-:_ : ∀ {m} → T → Abs (Telescope T m) → Telescope T (suc m)

telView : Type → ∃⟨ Telescope (Arg Type) ∩ Absₙ Type ⟩
telView (pi a (abs x b)) = let (_ , ts , t) = telView b
                           in -, (a -: abs x ts) , openAbs (abs x t)
telView e                = -, [] , mkAbsₙ [] e

untelView : ∀ {n} → Telescope (Arg Type) n → Absₙ Type n → Type
untelView []             ty = runAbsₙ ty
untelView (a -: abs x Γ) ty = pi a (abs x (untelView Γ (unAbs (closeAbs ty))))

telToArgInfoVec : ∀ {T n} → Telescope (Arg T) n → Vec ArgInfo n
telToArgInfoVec []                   = []
telToArgInfoVec (arg i _ -: abs _ Γ) = i ∷ telToArgInfoVec Γ

data View : ℕ → Set where
  2+  : ∀ n → View (suc (suc n))
  any : ∀ n → View n

data View2 : ℕ → ℕ → Set where
  zz  : View2 0 0
  ss  : ∀ m n → View2 (suc m) (suc n)
  any : ∀ {n m} → View2 m n

{-
showTele : ∀ {n} → Telescope (Arg Type) n → String
showTele []       = ""
showTele (Γ ,- record { unAbsₙ = arg _ x }) = showTele Γ ++ "(" ++ showType x ++ ") → "
-}

fType : Name → TC Type
fType nm = let open Reflection in do
  ty ← getType nm
  let (n , ts , mkAbsₙ xs _) = telView ty
  let infos = telToArgInfoVec ts
  let vars  = Vec.reverse (Vec.allFin n)
  let args  = Vec.zipWith (λ i k → arg i (var (Fin.toℕ k) [])) infos vars
  return (untelView ts $ mkAbsₙ xs $ def nm (Vec.toList args))

open import Category.Monad

monad : ∀ {ℓ} → RawMonad {ℓ} TC
monad = record { return = Reflection.return ; _>>=_ = Reflection._>>=_ }

import Data.List.Categorical as List
module T {ℓ} = List.TraversableM (monad {ℓ})
open T

module _ where

  open import Category.Monad.State
  open RawMonadState (StateTMonadState (List ℕ) monad)
  open import Data.List.Membership.DecPropositional ℕ._≟_

  termToPattern   : Term → StateT (List ℕ) TC Pattern
  termsToPatterns : List (Arg Term) → StateT (List ℕ) TC (List (Arg Pattern))

  termToPattern (var x [])   = do
    ns   ← get
    no _ ← return (x ∈? ns)
      where _ → pure dot
    put (x ∷ ns)
    pure (var ("var" ++ ℕₛ.show x))
  termToPattern (con c args) = do
    pargs ← termsToPatterns args
    return $ con c pargs
  termToPattern (lit l)      = return (lit l)
  termToPattern _            = return dot

  termsToPatterns []             = return []
  termsToPatterns (arg i t ∷ ts) = do
    p  ← termToPattern t
    ps ← termsToPatterns ts
    return (arg i p ∷ ps)

  renameVar : List ℕ → ℕ → ℕ
  renameVar π x with x ∈? π
  ... | yes p = Fin.toℕ (Any.index p)
  ... | no ¬p = x -- impossible?

fClauses : Name → TC (List Clause)
fClauses nm = let open Reflection in do
  (data-type pars cs) ← getDefinition nm
    where _ → {!!}
  forM cs $ λ cnm → do
    ty ← getType cnm
    let (n , ts , mkAbsₙ xs t) = telView ty
    (def nm′ args) ← return t
      where _ → {!!}
    yes p ← return (nm Name.≟ nm′)
      where _ → {!!}
    (pargs , π) ← termsToPatterns args []
    let infos = telToArgInfoVec ts
    let vars  = Vec.map (renameVar π ∘′ Fin.toℕ) $ Vec.reverse (Vec.allFin n)
    let args  = Vec.zipWith (λ i k → arg i (var k [])) infos vars
    return (clause pargs (con cnm (Vec.toList args)))

viewString : TC String
viewString = let open Reflection in do
  fty ← fType (quote View2)
  fcl ← fClauses (quote View2)
  return $ unlines
    $ Term.show fty
    ∷ List.map showClause fcl

mkView : Name → Name → TC ⊤
mkView v ty = let open Reflection in do
  viewTy ← fType ty
  viewCl ← fClauses ty
  declareDef (arg (arg-info visible relevant) v) viewTy
  defineFun v viewCl

unquoteDecl view  = mkView view (quote View)

half : ℕ → ℕ
half n with view n
... | 2+ m  = suc (half m)
... | any _ = zero

unquoteDecl view2 = mkView view2 (quote View2)

view2-invert : ∀ m n → view2 m n ≡ any → ¬ (m ≡ n)
view2-invert zero    n () refl
view2-invert (suc m) n () refl

eq? : DecidableEquality ℕ
eq? m n with view2 m n | inspect (view2 m) n
... | zz       | _      = yes refl
... | ss m' n' | _      = Dec.map′ (cong suc) ℕₚ.suc-injective (eq? m' n')
... | any      | [ eq ] = no (view2-invert m n eq)

macro

  runTC : TC String → Term → TC ⊤
  runTC tc hole = let open Reflection in do
    n ← tc
    unify hole (lit (string n))

_ : String
_ = {!!}
