module Lib

import Data.Buffer
import Data.Vect

%default total

export
failWith : String -> a
failWith str = assert_total (idris_crash str)

export
etaUnit : (t : ()) -> t === ()
etaUnit () = Refl

public export
record (*) (a, b : Type) where
  constructor (#)
  fst : a
  snd : b

public export
curry : ((a * b) -> r) -> a -> b -> r
curry f x y = f (x # y)

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
