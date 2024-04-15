module Lib

import Data.Buffer
import Data.Vect

%default total

||| Unsigned bytes are valid bounded natural numbers
||| Bits8 is a built-in type and so we have to postulate the proof
||| using `believe_me`. This is not however marked as unsafe.
export
bits8AsBoundedNat : (i : Bits8) -> (n : Nat ** So (n <= 255))
bits8AsBoundedNat i = (cast i ** believe_me Oh)


||| Runtime error
export
failWith : String -> a
failWith str = assert_total (idris_crash str)

||| Proof of eta for unit:
||| All terms are propositionally equal to the canonical constructor
export
etaUnit : (t : ()) -> t === ()
etaUnit () = Refl

||| Pairs
public export
record (*) (a, b : Type) where
  constructor (#)
  fst : a
  snd : b

public export
curry : ((a * b) -> r) -> a -> b -> r
curry f x y = f (x # y)

||| Proof of eta for pairs:
||| Every pair is propositionally equal to the pair constructor
||| applied to its projections
export
etaPair : (p : (a * b)) -> p === (fst p # snd p)
etaPair (t # u) = Refl

parameters (buf : Buffer)

  export
  setInts : Int -> Vect n Int -> IO ()
  setInts start [] = pure ()
  setInts start (i :: is)
    = do setInt buf start i
         setInts (start + 8) is

%spec a, b, vs, idx, k
public export
index : {0 b : a -> Type} ->
        (vs : Vect n a) -> (idx : Fin n) ->
        (k : (v : a) -> b v) -> b (index idx vs)
index (v :: _) FZ k = k v
index (_ :: vs) (FS idx) k = index vs idx k
