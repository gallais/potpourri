module Paleontology.Nat

import Data.Vect
import Data.DPair

%default total

public export
data Fossil : (Nat -> Type) -> (Nat -> Type) where
  Z : Fossil k Z
  S : k n -> Fossil k (S n)

public export
interface Dig (k : Nat -> Type) where

  %inline
  dig : k n -> Fossil k n

public export
greplicate : (0 k : Nat -> Type) -> Dig k => k n -> a -> Vect n a
greplicate _ pit a = case dig pit of
  Z      => []
  S pit' => a :: greplicate _ pit' a

public export
Dig (\ n => Vect n a) where

  dig [] = Z
  dig (_ :: tl) = S tl

vect : Vect 3 Int
vect = [0,1,2]

replicateV : Vect n elt -> a -> Vect n a
replicateV {elt} = greplicate (the (Nat -> Type) (\ n => Vect n elt))

data FTree : Nat -> Type -> Type where
  Leaf : a -> FTree Z a
  Node : FTree n (a, a) -> FTree (S n) a

Dig (\ n => Exists (FTree n)) where

  dig (Evidence _ (Leaf _)) = Z
  dig (Evidence _ (Node t)) = S (Evidence _ t)

ftree : FTree 3 Int
ftree = Node $ Node $ Node $ Leaf (((0,1),(2,3)),((4,5),(6,7)))

replicateF : FTree n _ -> a -> Vect n a
replicateF = greplicate (the (Nat -> Type) (\ n => (Exists (FTree n)))) . Evidence _
