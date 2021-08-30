module Generator

import Codata.BTree
import Data.Fin
import Data.List1
import Data.Vect
import Data.Random
import Data.RoseTree

%default total

public export
record Generator (a : Type) where
  constructor MkGenerator
  runGenerator : Nat -> Seed -> a

export
Functor Generator where
  map f (MkGenerator gen) = MkGenerator (\ n, s => f (gen n s))

export
Applicative Generator where
  pure a = MkGenerator (\ _, _ => a)
  MkGenerator genf <*> MkGenerator genx
    = MkGenerator $ \ n, s =>
      let (s1, s2) = split s in
      genf n s1 (genx n s2)

export
Monad Generator where
  MkGenerator gena >>= f
    = MkGenerator $ \ n, s =>
      let (s1, s2) = split s in
      runGenerator (f $ gena n s1) n s2

export
sized : (Nat -> Generator a) -> Generator a
sized f = MkGenerator $ \ n, s => runGenerator (f n) n s

export
resize : (n : Nat) -> Generator a -> Generator a
resize n (MkGenerator gena) = MkGenerator (const $ gena n)

export
promote : Rose (Generator a) -> Generator (Rose a)
promote r = MkGenerator $ \ n, s => map (\ gena => runGenerator gena n s) r

export
sample : Generator a -> List a
sample (MkGenerator gena) = do
  n <- [0..10]
  s <- toList $ splits Random.new 20
  pure (gena n s)

export
variant : Path -> Generator a -> Generator a
variant p (MkGenerator gena) = MkGenerator $ \ n, s => gena n (varySeed p s)

export
reallyUnsafeDelay : Generator (Generator a -> a)
reallyUnsafeDelay = MkGenerator $ \ n, s, (MkGenerator gena) => gena n s

export
reallyUnsafePromote : (r -> Generator a) -> Generator (r -> a)
reallyUnsafePromote f = map (. f) reallyUnsafeDelay

export
choose : (a : Type) -> Random a => Generator a
choose a @{p} = MkGenerator $ \ n, s => fst (random @{p} s)

namespace List1

  public export
  length : List1 a -> Nat
  length xxs = S (length xxs.tail)

  export
  fromList1 : (xxs : List1 a) -> Vect (length xxs) a
  fromList1 (x ::: xs) = x :: fromList xs

export
oneOf : List1 (Generator a) -> Generator a
oneOf genas = do
  k <- choose (Fin ?)
  index k (fromList1 genas)
