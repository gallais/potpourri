module CPSLib

import Data.Buffer
import Data.Vect

%default total

%inline %spec vs, k
public export
index1 : {0 b : a -> Type} ->
        (vs : Vect 1 a) -> (idx : Fin 1) ->
        (k : (v : a) -> b v) -> b (index idx vs)
index1 (v :: _) FZ k = k v

%inline %spec vs, k
public export
index2 : {0 b : a -> Type} ->
         (vs : Vect 2 a) -> (idx : Fin 2) ->
         (k : (v : a) -> b v) -> b (index idx vs)
index2 vs FZ k = k (index 0 vs)
index2 vs (FS FZ) k = k (index 1 vs)

public export
recindex : {n : Nat} -> {0 b : a -> Type} ->
        (vs : Vect n a) -> (idx : Fin n) ->
        (k : (v : a) -> b v) -> b (index idx vs)
recindex (v :: _) FZ k = k v
recindex (_ :: vs) (FS idx) k = recindex vs idx k

public export %inline
index : {n : Nat} -> {0 b : a -> Type} ->
        (vs : Vect n a) -> (idx : Fin n) ->
        (k : (v : a) -> b v) -> b (index idx vs)
index {n = 1} = index1
index {n = 2} = index2
index = recindex
