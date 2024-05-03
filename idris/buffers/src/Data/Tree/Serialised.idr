module Data.Tree.Serialised

import Data.Buffer.Indexed
import Data.Singleton
import Data.Vect

import Data.Linear.Notation
import Control.Linear.LIO

%default total

data Desc : Nat -> Type where
  None : Desc 0
  Byte : Desc 1
  Prod : {m : Nat} -> Desc m -> Desc n -> Desc (m + n)


etaUnit : (t : ()) -> t === ()
etaUnit () = Refl

etaPair : (p : (a, b)) -> p === (fst p, snd p)
etaPair (l, r) = Refl

namespace Data

  public export
  Meaning : Desc n -> Type
  Meaning None = ()
  Meaning Byte = Bits8
  Meaning (Prod x y) = (Meaning x, Meaning y)

  public export
  serialise : (d : Desc n) -> Meaning d -> Vect n Bits8
  serialise None v = []
  serialise Byte v = [v]
  serialise (Prod d e) (v, w) = serialise d v ++ serialise e w

namespace Serialise

  data Meaning : (r : Region) -> (start : Nat) -> (d : Desc n) -> (v : Meaning d) -> Type where
    MkMeaning :
      {0 d : Desc n} -> {0 v : Meaning d} ->
      {r : Region} ->
      {start : Nat} ->
      Owned r start (start + n) (serialise d v) -@
      Meaning r start d v

  split : {m : Nat} -> {0 d : Desc m} -> {0 v : Meaning d} ->
          {0 n : Nat} -> {0 e : Desc n} -> {0 w : Meaning e} ->
          Meaning r start (Prod d e) (v, w) -@
          LPair (Meaning r start d v) (Meaning r (start + m) e w)
  split (MkMeaning o)
    = let 1 olr = splitAt m o in
      let (ol # or) = olr in
      (MkMeaning ol # MkMeaning (rewrite sym $ plusAssociative start m n in or))

  (++) : {0 m : Nat} -> {0 d : Desc m} -> {0 v : Meaning d} ->
         {0 n : Nat} -> {0 e : Desc n} -> {0 w : Meaning e} ->
         Meaning r start d v -@ Meaning r (start + m) e w -@
         Meaning r start (Prod d e) (v, w)
  MkMeaning ol ++ MkMeaning or
    = MkMeaning (ol ++ rewrite plusAssociative start m n in or)

  pair : Singleton a -@ Singleton b -@ Singleton (a, b)
  pair (Val a) (Val b) = Val (a, b)

  deserialise : LinearIO io => (d : Desc n) -> {0 v : Meaning d} ->
                Meaning r start d v -@
                L1 io (LPair (Meaning r start d v) (Singleton v))
  deserialise None = rewrite etaUnit v in \ m => pure1 (m # Val ())
  deserialise Byte = \ (MkMeaning o) => do
    (o # b) <- getBits8 o 0
    pure1 (MkMeaning o # b)
  deserialise (Prod d e)
    = rewrite etaPair v in \ m =>
      do let 1 mlr = split m
         let (ml # mr) = mlr
         (ml # vl) <- deserialise d ml
         (mr # vr) <- deserialise e mr
         pure1 (ml ++ mr # pair vl vr)
