module Data.SnocList.AtIndex

%default total

||| @AtIndex witnesses the fact that a natural number encodes a membership proof.
||| It is meant to be used as a runtime-irrelevant gadget to guarantee that the
||| natural number is indeed a valid index.
public export
data AtIndex : (n : Nat) -> (x : a) -> (sx : SnocList a) -> Type where
  Z : AtIndex Z x (sx :< x)
  S : AtIndex n x sx -> AtIndex (S n) x (sx :< y)
