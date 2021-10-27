module Paleontology.Nat

import Data.Vect
import Data.DPair

%default total

data Fossil : (Nat -> Type) -> (Nat -> Type) where
  Z : Fossil k Z
  S : k n -> Fossil k (S n)

interface Dig (0 k : Nat -> Type) where

  %inline
  dig : k n -> Fossil k n

iteration : (0 p : Nat -> Type) ->
            (pZ : p Z) ->
            (pS : (0 n : Nat) -> p n -> p (S n)) -> -- note that n is runtime irrelevant
            (0 k : Nat -> Type) -> Dig k => k n -> p n
iteration p pZ pS k pit = case dig pit of
  Z      => pZ
  S pit' => pS _ (iteration p pZ pS k pit')

recursion : (0 p : Nat -> Type) ->
            (pZ : p Z) ->
            (pS : (n : Nat) -> p n -> p (S n)) ->
            (0 k : Nat -> Type) -> Dig k => k n -> p n
recursion p pZ pS k pit =
  let 0 p' : Nat -> Type
      p' n = (m : Nat ** (m = n, p m))

      pZ' : p' Z
      pZ' = (Z ** (Refl, pZ))

      pS' : (0 n : Nat) -> p' n -> p' (S n)
      pS' m (m ** (Refl, ih)) = (S m ** (Refl, pS m ih))
  in
  let (_ ** (Refl, v)) = iteration p' pZ' pS' k pit
  in v

greplicate : (0 k : Nat -> Type) -> Dig k => k n -> a -> Vect n a
greplicate _ pit a = case dig pit of
  Z      => []
  S pit' => a :: greplicate _ pit' a

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


decEq : Dig k => Dig l => k m -> l n -> Dec (m === n)
decEq km ln = case dig km of
  Z    => case dig ln of
    Z    => Yes Refl
    S ln => No absurd
  S km => case dig ln of
    Z    => No absurd
    S ln => case decEq km ln of
      Yes prf => Yes (cong S prf)
      No absurd => No (absurd . succInjective _ _)
