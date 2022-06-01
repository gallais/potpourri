||| An attempt at tackling
||| https://proofassistants.stackexchange.com/questions/1472/strictly-monotone-max-operation-for-constructive-brouwer-trees
module Joey

import Data.Nat
import Data.Nat.Order.Strict
import Control.Relation
import Data.Relation
import Data.Relation.Closure.Transitive
import Data.Relation.Closure.ReflexiveTransitive
import Decidable.Order.Strict
import AlmostFull

%default total

0 Alts1 : (rel : Rel a) -> Rel (a, a)
Alts1 rel = Or (\ p, q => fst p `rel` fst q) (\ p, q => fst p `rel` snd q)

0 Alts2 : (rel : Rel a) -> Rel (a, a)
Alts2 rel = Or (\ p, q => snd p `rel` fst q) (\ p, q => snd p `rel` snd q)

0 Alts : (rel : Rel a) -> Rel (a, a)
Alts rel = And (Alts1 rel) (Alts2 rel)


stepDown : TList (Alts rel) ~> Alts (TList rel)
stepDown (t :: ts) = ?tmp where

  snoc : {z : _} -> Alts (TList rel) x y -> Alts rel y z -> Alts (TList rel) x z
  snoc (ps , qs) pq = (snoc1 ps pq, snoc2 qs pq) where

    snoc1 : Alts1 (TList rel) x y -> Alts rel y z -> Alts1 (TList rel) x z
    snoc1 (Left ps)  (Left p , q)       = Left (ps :< p)
    snoc1 (Left ps)  (Right p, q)       = Right (ps :< p)
    snoc1 (Right ps) (p      , Left q)  = Left (ps :< q)
    snoc1 (Right ps) (p      , Right q) = Right (ps :< q)

    snoc2 : Alts2 (TList rel) x y -> Alts rel y z -> Alts2 (TList rel) x z
    snoc2 (Left ps)  (Left p , q)       = Left (ps :< p)
    snoc2 (Left ps)  (Right p, q)       = Right (ps :< p)
    snoc2 (Right ps) (p      , Left q)  = Left (ps :< q)
    snoc2 (Right ps) (p      , Right q) = Right (ps :< q)

  go : Alts (TList rel) x y ->
       RTList (Alts rel) y z ->
       Alts (TList rel) x z
  go acc [] = acc
  go acc (t :: ts) = go (snoc acc t) ts

0 Compat : (t, rel : Rel a) -> Type
Compat t rel = {w, x, y, z : a} -> TList t w x -> rel x y -> TList t y z -> TList t w z

alts : (0 t : Rel a) ->
  AlmostFull rel ->
  NoInfiniteDescent t rel ->
  Compat t rel ->
  Rec (Alts t) p -> (v : (a, a)) -> p v
alts t af prf cmp = almostFullInduction af' prf' where

  0 T : Rel (a, a)
  T = Alts t

  0 R : Rel (a, a)
  R = And (rel `on` Builtin.fst) (rel `on` Builtin.snd)

  af' : AlmostFull R
  af' = almostFullPair af af

  prf' : NoInfiniteDescent T R
  prf' (x1, x2) (y1, y2) (ts, (p, q)) = case stepDown {rel = t} ts of
    (Left ps, pat2) => prf x1 y1 (ps , p)
    (Right ps, Left qs) => prf x1 y1 (cmp ps q qs, p)
    (Right ps, Right qs) => prf x2 y2 (qs, q)


------------------------------------------------------------------------------
-- Example
------------------------------------------------------------------------------

compatLTLTE : Compat LT LTE
compatLTLTE wx xy yz = [transitive (tlist wx) (transitive (lteSuccRight xy) (tlist yz))]

||| Unsafe weird
covering
unsafeWeird : (Nat, Nat) -> Nat
unsafeWeird (0, _) = 1
unsafeWeird (_, 0) = 1
unsafeWeird (S x, S y) = unsafeWeird (x, y) + unsafeWeird (y, x)

||| Safe weird, deploying max-bound:
weird : (Nat, Nat) -> Nat
weird = alts LT almostFullLTE (noInfiniteDescent transitive) compatLTLTE rec

  where

   rec : Rec (Alts LT) (\_ => Nat)
   rec (0, _)     ih = 1
   rec (_, 0)     ih = 1
   rec (S x, S y) ih = ih (x , y) (Left reflexive, Right reflexive)
                     + ih (y , x) (Right reflexive, Left reflexive)
