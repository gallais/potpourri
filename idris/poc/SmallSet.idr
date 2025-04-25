module SmallSet

import Data.Bits
import Data.DPair
import Data.List.AtIndex
import Decidable.Equality

%default total


record SmallSet (vs : List a) where
  constructor MkSmallSet
  encoding : Integer
  0 valid  : encoding `shiftL` length vs === 0


data IsYes : Dec a -> Type where
  ItIsYes : (v : a) -> IsYes (Yes v)

fromYes : IsYes {a} d -> a
fromYes (ItIsYes v) = v

emptySet : SmallSet vs
emptySet = MkSmallSet 0 ?prf

union : SmallSet vs -> SmallSet vs -> SmallSet vs
union (MkSmallSet e1 prf1) (MkSmallSet e2 prf2)
  = MkSmallSet (e1 .|. e2) ?prf3

intersection : SmallSet vs -> SmallSet vs -> SmallSet vs
intersection (MkSmallSet e1 prf1) (MkSmallSet e2 prf2)
  = MkSmallSet (e1 .&. e2) ?prf4

%spec dec
insert : DecEq a => (v : a) -> (dec : IsYes (find v vs)) => SmallSet vs -> SmallSet vs
insert @{_} v @{idx} (MkSmallSet enc val)
  = let (Element n prf) = fromYes idx in
    MkSmallSet (setBit enc n) ?b

%spec dec
remove : DecEq a => (v : a) -> (dec : IsYes (find v vs)) => SmallSet vs -> SmallSet vs
remove @{_} v @{idx} (MkSmallSet enc val)
  = let (Element n prf) = fromYes idx in
    MkSmallSet (clearBit enc n) ?bc

%spec dec
elem : DecEq a => (v : a) -> (dec : IsYes (find v vs)) => SmallSet vs -> Bool
elem @{_} v @{idx} (MkSmallSet enc val)
  = let (Element n prf) = fromYes idx in
    testBit enc n

-- TODO:
-- Prove invariants are respected
-- Prove `get v (remove v vs) === False`
-- Prove `get v (insert v vs) === True`
-- Prove `get v (insert w vs) === get v vs` when `v /= w`
-- Prove `get v (remove w vs) === get v vs` when `v /= w`


test :
  let s := insert 3 (insert 1 (the (SmallSet [1..5]) emptySet)) in
  So ((1 `elem` s) && not (4 `elem` s))
test = Oh
