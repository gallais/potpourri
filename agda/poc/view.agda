module poc.view where

open import Data.Unit using (⊤)
open import Reflection hiding (return; _>>_; _>>=_)
open import Reflection.Term as Term
open import Reflection.Argument as Arg
open import Reflection.Definition
open import Reflection.Pattern
open import Reflection.Argument.Information
open import Reflection.Name as Name
open import Reflection.Abstraction

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; _<ᵇ_; _≤_; ∣_-_∣)
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

private

  record Absₙ (T : Set) (n : ℕ) : Set where
    constructor mkAbsₙ
    field
      names  : Vec String n
      unAbsₙ : T

  openAbs : ∀ {T n} → Abs (Absₙ T n) → Absₙ T (suc n)
  openAbs (abs x (mkAbsₙ xs t)) = mkAbsₙ (x ∷ xs) t

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

parametersOf : Name → TC ℕ
parametersOf cnm = let open Reflection in do
  ty ← getType cnm
  let (_ , _ , mkAbsₙ _ t) = telView ty
  (def nm args) ← return t where
    _ → typeError $ strErr "The impossible has happened: the constructor"
                  ∷ nameErr cnm
                  ∷ strErr "does not construct a value of a datatype."
                  ∷ []
  (data-type pars _) ← getDefinition nm where
    _ → typeError $ nameErr nm
                  ∷ strErr "is not a datatype \
                           \so I cannot generate a view for it."
                  ∷ []
  return pars

module _ where

  open import Category.Monad.State
  open RawMonadState (StateTMonadState (List ℕ) monad)
  open import Data.List.Membership.DecPropositional ℕ._≟_

  liftTC : ∀ {a} {A : Set a} {S : Set a} → TC A → StateT S TC A
  liftTC tc s = bindTC tc (λ a → Reflection.return (a , s))

  termToPattern    : Term → StateT (List ℕ) TC Pattern
  termsToPatterns  : List (Arg Term) → StateT (List ℕ) TC (List (Arg Pattern))
  termsToPatterns' : ℕ → List (Arg Term) → StateT (List ℕ) TC (List (Arg Pattern))

  termToPattern (var x [])   = do
    ns   ← get
    no _ ← return (x ∈? ns)
      where _ → pure dot
    put (x ∷ ns)
    pure (var ("var" ++ ℕₛ.show x))
  termToPattern (con c args) = do
    pars  ← liftTC $ parametersOf c
    pargs ← termsToPatterns' pars args
    return $ con c pargs
  termToPattern (lit l)      = return (lit l)
  termToPattern _            = return dot

  termsToPatterns' zero    ts       = termsToPatterns ts
  termsToPatterns' (suc n) (t ∷ ts) = termsToPatterns' n ts
  termsToPatterns' (suc n) []       = liftTC $
    typeError $ strErr "The impossible has happened: \
                       \fewer arguments than parameters"
              ∷ []

  termsToPatterns []           = return []
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
  (data-type pars cs) ← getDefinition nm where
    _ → typeError $ nameErr nm
                  ∷ strErr "is not a datatype \
                           \so I cannot generate a view for it."
                  ∷ []
  forM cs $ λ cnm → do
    ty ← getType cnm
    let (n , ts , mkAbsₙ xs t) = telView ty
    (def nm′ args) ← return t where
      _ → typeError $ strErr "The impossible has happened: the constructor"
                    ∷ nameErr cnm
                    ∷ strErr "does not construct a value of a datatype."
                    ∷ []
    yes p ← return (nm Name.≟ nm′) where
      _ → typeError $ strErr "The impossible has happened: the constructor"
                    ∷ nameErr cnm
                    ∷ strErr "does not construct a value of type"
                    ∷ nameErr nm
                    ∷ []
    (pargs , π) ← termsToPatterns args []
    let infos = telToArgInfoVec ts
    let vars  = Vec.map (renameVar π ∘′ Fin.toℕ) $ Vec.reverse (Vec.allFin n)
    let args  = Vec.zipWith (λ i k → arg i (var k [])) infos vars
    return (clause pargs (con cnm (Vec.toList args)))

mkView : Name → Name → TC ⊤
mkView v ty = let open Reflection in do
  viewTy ← fType ty
  viewCl ← fClauses ty
  declareDef (arg (arg-info visible relevant) v) viewTy
  defineFun v viewCl


data View : ℕ → Set where
  2+  : ∀ n → View (suc (suc n))
  any : ∀ {n} → View n

unquoteDecl view  = mkView view (quote View)

half : ℕ → ℕ
half n with view n
... | 2+ m = suc (half m)
... | any  = zero

half-dist : ∀ n → ∣ 2 * half n - n ∣ ≤ 1
half-dist n with view n | inspect view n
half-dist 0 | any | _ = ℕ.z≤n
half-dist 1 | any | _ = ℕ.s≤s ℕ.z≤n
... | 2+ m | _ = let open ℕₚ.≤-Reasoning; h = half m in begin
  ∣ h + (suc h + 0) - suc m ∣ ≡⟨ cong ∣_- suc m ∣ (ℕₚ.+-comm h (suc h + 0)) ⟩
  ∣ (h + 0) + h     - m     ∣ ≡⟨ cong ∣_- m ∣ (ℕₚ.+-comm (h + 0) h) ⟩
  ∣ 2 * h           - m     ∣ ≤⟨ half-dist m ⟩
  1                           ∎

data View2 : ℕ → ℕ → Set where
  zz  : View2 0 0
  ss  : ∀ m n → View2 (suc m) (suc n)
  any : ∀ {n m} → View2 m n

unquoteDecl view2 = mkView view2 (quote View2)

view2-invert : ∀ m n → view2 m n ≡ any → ¬ (m ≡ n)
view2-invert zero    n () refl
view2-invert (suc m) n () refl

eq? : DecidableEquality ℕ
eq? m n with view2 m n | inspect (view2 m) n
... | zz       | _      = yes refl
... | ss m' n' | _      = Dec.map′ (cong suc) ℕₚ.suc-injective (eq? m' n')
... | any      | [ eq ] = no (view2-invert m n eq)

data Empty? {a} {A : Set a} : List A → Set a where
  yes : Empty? []
  no  : ∀ x xs → Empty? (x ∷ xs)

unquoteDecl empty? = mkView empty? (quote Empty?)

sum : List ℕ → ℕ
sum xs with empty? xs
... | yes      = 0
... | no hd tl = hd + sum tl
