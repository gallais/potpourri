module poc.view where

open import Data.Unit
open import Reflection
open import Data.Bool.Base
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<ᵇ_)
import Data.Nat.Show as ℕₛ
import Data.Fin.Base as Fin
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product
open import Data.String
open import Function
open import Relation.Nary
open import Relation.Binary.PropositionalEquality

unArg : ∀ {A : Set} → Arg A → A
unArg (arg _ e) = e

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
    field unAbsₙ : T

  mkAbsₙ : ∀ {T n} → T → Absₙ T n
  mkAbsₙ t = record { unAbsₙ = t }

  wkAbsₙ : ∀ {T n} → Absₙ T n → Absₙ T (suc n)
  wkAbsₙ t .Absₙ.unAbsₙ = t .Absₙ.unAbsₙ

  unAbsₙTerm : ∀ {n} → Absₙ Term n → Term
  unAbsₙTerm {n} t = raiseTerm (initRaise n) (t .Absₙ.unAbsₙ)

data Telescope (T : Set) : ℕ → Set where
  []   : Telescope T 0
  _,-_ : ∀ {m} → Telescope T m → Absₙ T m → Telescope T (suc m)

telView : Type → ∃⟨ Telescope (Arg Type) ∩ Absₙ Type ⟩
telView (pi a (abs _ b)) = let (_ , (as , r)) = telView b
                           in -, (as ,- mkAbsₙ a , wkAbsₙ r)
telView e                = -, ([] , mkAbsₙ e)


telToArg-infoVec : ∀ {T n} → Telescope (Arg T) n → Vec Arg-info n
telToArg-infoVec = Vec.reverse ∘ go where

  go : ∀ {T n} → Telescope (Arg T) n → Vec Arg-info n
  go []       = []
  go (Γ ,- a) with Absₙ.unAbsₙ a
  ... | arg i _ = i ∷ go Γ

data View : ℕ → Set where
  2+  : ∀ n → View (suc (suc n))
  any : ∀ n → View n

showTerm : Term → String
showType : Type → String
showArgTerms : List (Arg Term) → String

showTerm = showType

showType (var x args) = ℕₛ.show x
showType (con c args) = showName c ++ " " ++ showArgTerms args
showType (def f args) = showName f ++ " " ++ showArgTerms args
showType (lam v t) = "lam"
showType (pat-lam cs args) = "plam"
showType (pi (arg _ a) (abs _ b)) = "Π" ++ showType a ++ showType b
showType (sort (set t)) = "Set ?"
showType (sort (lit n)) = "Set " ++ ℕₛ.show n
showType (sort unknown) = "?"
showType (lit l) = "lit"
showType (meta x x₁) = "?"
showType unknown = "?"

showArgTerms [] = ""
showArgTerms (arg i x ∷ xs) = showTerm x ++ " " ++ showArgTerms xs

showTele : ∀ {n} → Telescope (Arg Type) n → String
showTele []       = ""
showTele (Γ ,- record { unAbsₙ = arg _ x }) = showTele Γ ++ "(" ++ showType x ++ ") → "

fType : Name → TC Type
fType nm = do
  ty ← getType nm
  let (n , ts , t) = telView ty
  let infos = telToArg-infoVec ts
  let vars  = Vec.reverse (Vec.allFin n)
  let args  = Vec.zipWith (λ i k → arg i (var (Fin.toℕ k) [])) infos vars
  return (def nm (Vec.toList args))


view : TC String
view = do
  fty ← fType (quote View)
  return $ showType fty

macro

  runTC : TC String → Term → TC ⊤
  runTC tc hole = do
    n ← tc
    unify hole (lit (string n))

_ : String
_ = {!!}
