module Data.Buffer.Indexed

import Data.Buffer as B
import Data.Nat
import Data.Fin
import Data.Vect
import Data.Singleton

import Control.Linear.LIO
import Data.Linear.Notation

public export
after : (m : Nat) -> Fin (m + S n)
after 0 = FZ
after (S k) = FS (after k)

public export
lookup : Vect size a -> Fin size -> a
lookup vs k = index k vs

public export
update : Vect size a -> Fin size -> a -> Vect size a
update (_ :: vs) FZ w = w :: vs
update (v :: vs) (FS k) w = v :: update vs k w

%unsafe
unsafeMkSingleton : (0 x : a) -> (val : a) -> Singleton x
unsafeMkSingleton x val = believe_me (Val val)

namespace SnocVect

  public export
  addz : Nat -> Nat -> Nat
  addz 0 n = n
  addz (S m) n = addz m (S n)

  public export
  adds : Nat -> Nat -> Nat
  adds m 0 = m
  adds m (S n) = adds (S m) n

  public export
  data SnocVect : Nat -> Type -> Type where
    Lin : SnocVect Z a
    (:<) : SnocVect n a -> a -> SnocVect (S n) a

  public export
  Functor (SnocVect n) where
    map f [<] = [<]
    map f (xs :< x) = map f xs :< f x

  public export
  (<><) : SnocVect m a -> Vect n a -> SnocVect (adds m n) a
  vs <>< [] = vs
  vs <>< (w :: ws) = (vs :< w) <>< ws

  public export
  (<>>) : SnocVect m a -> Vect n a -> Vect (addz m n) a
  [<] <>> ws = ws
  (vs :< v) <>> ws = vs <>> (v :: ws)

  export
  mapChips :
    (f : a -> b) ->
    (sx : SnocVect m a) ->
    (xs : Vect n a) ->
    map f (sx <>> xs) === (map f sx <>> map f xs)
  mapChips f [<] xs = Refl
  mapChips f (sx :< x) xs = mapChips f sx (x :: xs)


afterz : (m : Nat) -> {0 n : Nat} -> Fin n -> Fin (addz m n)
afterz 0 k = k
afterz (S m) k = afterz m (FS k)

lookupAfterz :
  (vs : SnocVect m a) -> {ws : Vect n a} ->
  (k : Fin n) ->
  lookup (vs <>> ws) (afterz m k) === lookup ws k
lookupAfterz [<] k  = Refl
lookupAfterz (vs :< v) k = lookupAfterz vs (FS k)

updateAfterz :
  (vs : SnocVect m a) -> {ws : Vect n a} ->
  (k : Fin n) -> (v : a) ->
  update (vs <>> ws) (afterz m k) v === (vs <>> update ws k v)
updateAfterz [<] k v = Refl
updateAfterz (vs :< _) k v = updateAfterz vs (FS k) v

namespace Vect

  public export
  data View : Vect n a -> Type where
    Nil : View []
    (::) : {n : Nat} -> (0 x : a) -> (0 xs : Vect n a) -> View (x :: xs)

  public export
  view : {n : Nat} -> (0 xs : Vect n a) -> View xs
  view {n = 0} [] = []
  view {n = S n} (x :: xs) = x :: xs

namespace ReadWrite

  ||| This is a wrapper for `Buffer` ensuring users do not
  ||| get access to the raw buffer and so cannot manually
  ||| update it using primitives bound in `Data.Buffer`.
  export
  record Region where
    constructor MkRegion
    getBuffer : Buffer

  ||| (Buffer l start end vs) can be understood as a proof of
  ||| ownership of the portion of the region named `l` between
  ||| `start` (inclusive) and `end` (exclusive) whose content is
  ||| `vs`.
  |||
  ||| `copyOfStart` is a runtime copy of the index `start`
  ||| `content`     is the underlying buffer for the (whole!) region `l`
  |||
  |||
  ||| /!\ It is crucial for invariants preservation that this
  ||| definition is not `public export`. This way users are
  ||| forced to use our invariants-safe functions to manipulate
  ||| buffers.
  ||| The first invariant is that `l` is a unique label for the
  ||| region: all the buffers indexed by the same `l` are assumed
  ||| to have the same `content`.
  ||| The second invariant is that the bytes stored in `content`
  ||| between indices `start` and `end` are exactly the ones listed
  ||| in the `vs` index.
  export
  data Owned :
      (region : Region) ->
      (start : Nat) ->
      {size : Nat} ->
      (end : Nat) ->
      (vs : Vect size Bits8) ->
      Type where
    MkOwned :
      {0 start, size, end : Nat} ->
      {0 values : Vect size Bits8} ->
      (0 _ : start + size === end) ->
      Owned region start end values

------------------------------------------------------------------------
-- Pure operations

  ||| We can split a buffer like we would split a vector:
  ||| if it is known to contain `vs ++ ws` and we know `m`
  ||| the size of `vs` then we can take it apart and turn
  ||| into two proofs of ownership:
  ||| one for the portion containing `vs`
  ||| and one for the one containing `ws`.
  export
  splitAt :
    (m : Nat) -> {0 vs : Vect m Bits8} ->
    {0 n : Nat} -> {0 ws : Vect n Bits8} ->
    Owned region start {size = m + n} end (vs ++ ws) -@
    LPair (Owned region start (start + m) vs)
          (Owned region (start + m) end ws)
  splitAt m (MkOwned Refl)
    = MkOwned reflexive
    # MkOwned (symmetric (plusAssociative _ _ _))

  ||| This definition is the first to explicitly take advantage
  ||| of the assumption that region labels are unique. If we own
  ||| two contiguous region segments, we can put them together
  ||| and obtain a proof that we own the combined segments.
  export
  (++) :
    Owned region start middle vs -@
    Owned region middle end ws -@
    Owned region start end (vs ++ ws)
  MkOwned Refl ++ MkOwned Refl
    = MkOwned (plusAssociative _ _ _)

  export
  curry :
    (m : Nat) -> {0 vs : Vect m Bits8} ->
    {0 n : Nat} -> {0 ws : Vect n Bits8} ->
    (Owned region start end (vs ++ ws) -@ a) -@
    (Owned region start (start + m) vs -@ Owned region (start + m) end ws -@ a)
  curry m k ol or = k (ol ++ or)

  export
  uncurry :
    (m : Nat) -> {0 vs : Vect m Bits8} ->
    {0 n : Nat} -> {0 ws : Vect n Bits8} ->
    (Owned region start (start + m) vs -@ Owned region (start + m) end ws -@ a) -@
    (Owned region start end (vs ++ ws) -@ a)
  uncurry m k o = let 1 olr = splitAt m o in let (ol # or) = olr in k ol or

  ||| Getting rid of a proof of ownership if we do not need
  ||| it anymore.
  export
  free : Owned region start end vs -@ ()
  free (MkOwned _) = ()

  ||| By combining `splitAt` and `free`, we can drop the
  ||| initial segment of a buffer.
  export
  drop :
    (m : Nat) -> {0 vs : Vect m Bits8} ->
    Owned region start {size = m + n} end (vs ++ ws) ->
    Owned region (start + m) {size = n} end ws
  drop m buf
    = let (trash # rest) = splitAt m buf in
      let () = free trash in
      rest

  ||| By combining `splitAt` and `free`, we can drop the
  ||| final segment of a buffer.
  export
  take :
    (m : Nat) -> {0 vs : Vect m Bits8} ->
    {0 n : Nat} -> {0 ws : Vect n Bits8} ->
    Owned region start {size = m + n} end (vs ++ ws) ->
    Owned region start {size = m} (start + m) vs
  take m buf
    = let (rest # trash) = splitAt m buf in
      let () = free trash in
      rest

------------------------------------------------------------------------
-- Read and write operations

  export %inline
  getBits8 :
    {region : Region} -> {start : Nat} ->
    LinearIO io =>
    (1 _ : Owned region start end vs) ->
    (idx : Fin size) ->
    L1 io (LPair (Owned region start end vs) (Singleton (lookup vs idx)))
  getBits8 (MkOwned valid) idx
    = do w <- B.getBits8 (getBuffer region) (cast (start + cast idx))
         pure1 (MkOwned valid # unsafeMkSingleton (lookup vs idx) w)

  %hide B.getBits8

  export %inline
  setBits8 :
    {region : Region} -> {start : Nat} ->
    LinearIO io =>
    (1 _ : Owned region start end vs) ->
    (idx : Fin size) ->
    (val : Bits8) ->
    L1 io (Owned region start end (update vs idx val))
  setBits8 (MkOwned valid) idx v
    = do B.setBits8 (getBuffer region) (cast (start + cast idx)) v
         pure1 (MkOwned valid)

  %hide B.setBits8

export
map :
  {start, size : Nat} -> {region : Region} -> {0 vs : Vect size Bits8} ->
  LinearIO io =>
  (f : Bits8 -> Bits8) ->
  (1 _ : Owned region start end vs) ->
  L1 io (Owned region start end (map f vs))
map f = loop [<] (view vs) where

  loop :
    {m : Nat} ->
    (0 acc : SnocVect m Bits8) ->
    {0 rest : Vect n Bits8} ->
    View rest ->
    (1 _ : Owned region start end (map f acc <>> rest)) ->
    L1 io (Owned region start end (map f (acc <>> rest)))
  loop acc [] buf
    = pure1 $ rewrite mapChips f acc [] in buf
  loop acc (v :: vs) buf
    = do buf # val <- getBits8 buf (afterz m FZ)
         let Val v = the (Singleton v) $ replace {p = Singleton} (lookupAfterz (map f acc) FZ) val
         buf <- setBits8 buf (afterz m FZ) (f v)
         let buf = replace {p = Owned _ _ _} (updateAfterz (map f acc) FZ (f v)) buf
         loop (acc :< v) (view vs) buf
