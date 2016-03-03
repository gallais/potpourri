module BN where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product as Product
open import Data.Fin
open import Data.Maybe as Maybe
open import Data.Vec
open import Data.String as String
open import Relation.Nullary

infixr 7 _`×_
data Desc : Set₁ where
  `Σ   : (A : Set) (d : A → Desc) → Desc
  `K   : Set → Desc
  `X   : Desc
  _`×_ : Desc → Desc → Desc
  `⊤   : Desc

desc : Desc → Set → Set
desc (`Σ A d) X = Σ[ a ∈ A ] desc (d a) X
desc (d `× e) X = desc d X × desc e X
desc (`K A)   X = A
desc `X       X = X
desc `⊤       X = ⊤

infix 5 _::_
record Constructor : Set₁ where
  constructor _::_
  field
    name : String
    tele : Desc
open Constructor

record Datatype : Set₁ where
  constructor mkDatatype
  field
    size  : ℕ
    names : Vec String size
    teles : Vec Desc   size
open Datatype

infixr 3 _<|>_
_<|>_ : Constructor → Datatype → Datatype
nm :: dc <|> mkDatatype n nms dcs = mkDatatype (suc n) (nm ∷ nms) (dc ∷ dcs)

■ : Datatype
■ = mkDatatype 0 [] []

Tree : Datatype
Tree = "Leaf" :: `⊤
   <|> "Node" :: `X `× `K ℕ `× `X
   <|> ■

data μ (d : Datatype) : Set where
  mkμ : (c : String) (k : Fin (size d)) (pr : names d [ k ]= c) →
        desc (lookup k (teles d)) (μ d) → μ d

isJust : {A : Set} → Maybe A → Set
isJust (just x) = ⊤
isJust nothing  = ⊥

fromJust : {A : Set} (ma : Maybe A) {pr : isJust ma} → A
fromJust (just a) = a
fromJust nothing {}

findIndex : (str : String) {n : ℕ} (strs : Vec String n) → Maybe (∃ λ k → strs [ k ]= str)
findIndex str [] = nothing
findIndex str (x ∷ strs) with str String.≟ x | findIndex str strs
... | yes p | r rewrite p = just (zero , here)
... | no ¬p | r = Maybe.map (Product.map suc there) r

tree : μ Tree
tree = mkμ "Node" (suc zero) (there here) (mkμ "Leaf" zero here tt , 3 , mkμ "Leaf" zero here tt)

cons : {d : Datatype} (str : String) {pr : isJust (findIndex str (names d))} →
       desc (let (k , p) = fromJust _ {pr} in lookup k (teles d)) (μ d) → μ d
cons str {pr} ds = let (k , p) = fromJust _ {pr} in mkμ str k p ds

tree′ : μ Tree
tree′ = cons "Node" (cons "Leaf" tt , 3 , cons "Leaf" tt)
