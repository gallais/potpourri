module Data.Buffer.Indexed

import Data.Bits
import Data.Buffer as B
import Data.Fin
import Data.List
import Data.List.HasLength
import Data.Nat
import Data.DPair
import Data.Singleton
import Data.SnocList
import Data.SnocList.HasLength

import Control.Linear.LIO
import Data.Linear.LMaybe
import Data.Linear.Notation

import System.Clock
import System
import System.Concurrency
import System.Concurrency.Linear

import Syntax.PreorderReasoning

%default total

%unsafe
unsafeMkSingleton : (0 x : a) -> (val : a) -> Singleton x
unsafeMkSingleton x val = believe_me (Val val)

record WithVal (a, b : Type) where
  constructor (#)
  1 fst : a
  snd : b

namespace ReadWrite

  ||| This is a wrapper for `Buffer` ensuring users do not
  ||| get access to the raw buffer and so cannot manually
  ||| update it using primitives bound in `Data.Buffer`.
  export
  record Region where
    constructor MkRegion
    getBuffer : Buffer

  ||| (Owner r start end vs) can be understood as a proof of
  ||| ownership of the portion of the region named `r` between
  ||| `start` (inclusive) and `end` (exclusive) whose content is
  ||| `vs`.
  |||
  ||| /!\ It is crucial for invariants preservation that this
  ||| definition is not `public export`. This way users are
  ||| forced to use our invariants-safe functions to manipulate
  ||| buffers.
  ||| The first invariant is that different programs can own different
  ||| slices of the same regions but owernship proofs should always be
  ||| unique and non-overlapping.
  |||
  ||| The second invariant is that the bytes stored in the region
  ||| between indices `start` and `end` are exactly the ones listed
  ||| in the `vs` index.
  export
  data Owned :
      (region : Region) ->
      (start, end : Nat) ->
      (vs : List Bits8) ->
      Type where
    MkOwned :
      (region : Region) ->
      {0 start, end : Nat} ->
      (0 _ : start + length values === end) ->
      Owned region start end values

  export
  lengthValue :
    Owned region start end vs ->
    length vs === minus end start
  lengthValue (MkOwned _ size) = Calc $
    |~ length vs
    ~~ minus (start + length vs) start ..<( minusPlus start )
    ~~ minus end start ..>( cong (`minus` start) size )

  export
  0 hasLength :
    Owned region start end vs ->
    HasLength (minus end start) vs
  hasLength buf = rewrite sym $ lengthValue buf in hasLength vs

  export
  length : {start, end : Nat} ->
           Owned region start end vs -@
           LPair (Subset Nat (\ n => HasLength n vs)) (Owned region start end vs)
  length (MkOwned region size)
    = Element (minus end start) (hasLength (MkOwned region size))
    # MkOwned region size


  export
  reindex :
    (0 _ : vs === ws) ->
    Owned region start end vs -@
    Owned region start end ws
  reindex Refl buf = buf

  public export
  record DynBuffer (size : Nat) where
    constructor MkDynBuffer
    {0 newregion : Region}
    {0 content : List Bits8}
    1 owned : Owned newregion 0 size content

  export
  allocate : LinearIO io => (size : Nat) -> L1 io (LMaybe (DynBuffer size))
  allocate size = do
    Just buf <- newBuffer (cast size)
      | _ => pure1 Nothing
    ------------------------------------------------------------
    -- postulated: whatever uninitialised memory is given to us!
    let 0 Values     : List Bits8
    let 0 ValuesSize : length Values === size
    ------------------------------------------------------------
    let region : Region = MkRegion buf
    let owned  : Owned region 0 size Values
      := MkOwned region ValuesSize
    pure1 $ Just $ MkDynBuffer {content = Values} owned

------------------------------------------------------------------------
-- Pure operations

  lengthAppend : (vs, ws : List a) -> length (vs ++ ws) === length vs + length ws
  lengthAppend [] ws = Refl
  lengthAppend (_ :: vs) ws = cong S (lengthAppend vs ws)

  ||| We can split a buffer like we would split a vector:
  ||| if it is known to contain `vs ++ ws` and we know `m`
  ||| the size of `vs` then we can take it apart and turn
  ||| into two proofs of ownership:
  ||| one for the portion containing `vs`
  ||| and one for the one containing `ws`.
  export
  splitAt :
    {0 vs, ws : List Bits8} ->
    {m : Nat} -> (0 _ : HasLength m vs) ->
    Owned region start end (vs ++ ws) -@
    LPair (Owned region start (start + m) vs)
          (Owned region (start + m) end ws)
  splitAt hlvs (MkOwned region size)
    = MkOwned region lsize # MkOwned region rsize

    where

    0 lvs : length vs === m
    lvs = hasLengthUnique (hasLength vs) hlvs

    lsize : start + length vs === start + m
    lsize = cong (start +) lvs

    rsize : start + m + length ws === end
    rsize = Calc $
      |~ start + m + length ws
      ~~ start + length vs + length ws
         ..<( cong (\ m => start + m + length ws) lvs )
      ~~ start + (length vs + length ws)
         ..<( plusAssociative _ _ _ )
      ~~ start + length (vs ++ ws)
         ..<( cong (start +) (lengthAppend vs ws) )
      ~~ end ..>( size )

  ||| This definition is the first to explicitly take advantage
  ||| of the assumption that region labels are unique. If we own
  ||| two contiguous region segments, we can put them together
  ||| and obtain a proof that we own the combined segments.
  export
  (++) :
    Owned region start middle vs -@
    Owned region middle end ws -@
    Owned region start end (vs ++ ws)
  MkOwned region lsize ++ MkOwned region rsize
    = MkOwned region size

    where

    size : start + length (vs ++ ws) = end
    size = Calc $
      |~ start + length (vs ++ ws)
      ~~ start + (length vs + length ws)
         ..>( cong (start +) (lengthAppend vs ws) )
      ~~ start + length vs + length ws
         ..>( plusAssociative _ _ _ )
      ~~ middle + length ws
         ..>( cong (+ length ws) lsize )
      ~~ end
         ..>( rsize )

  export
  curry :
    {0 vs, ws : List Bits8} ->
    (m : Nat) -> (0 _ : length vs === m) ->
    (Owned region start end (vs ++ ws) -@ a) -@
    (Owned region start (start + m) vs -@ Owned region (start + m) end ws -@ a)
  curry m lvs k ol or = k (ol ++ or)

  export
  uncurry :
    {0 vs, ws : List Bits8} ->
    {m : Nat} -> (0 lvs : HasLength m vs) ->
    (Owned region start (start + m) vs -@ Owned region (start + m) end ws -@ a) -@
    (Owned region start end (vs ++ ws) -@ a)
  uncurry lvs k o = let 1 olr = splitAt lvs o in let (ol # or) = olr in k ol or

  ||| Getting rid of a proof of ownership if we do not need
  ||| it anymore.
  export
  free : Owned region start end vs -@ ()
  free (MkOwned region size) = ()

------------------------------------------------------------------------
-- Read and write operations

  -- TODO: should I just get rid of the IO nonsense?!

  export %inline
  getBits8 :
    LinearIO io =>
    {start, end : Nat} ->
    (1 _ : Owned region start end vs) ->
    (idx : Nat) -> (0 _ : InBounds idx vs) ->
    L1 io (WithVal (Owned region start end vs) (Singleton (index idx vs)))
  getBits8 (MkOwned region size) idx bnds
    = do w <- B.getBits8 (getBuffer region) (cast (start + cast idx))
         pure1 (MkOwned region size # unsafeMkSingleton (index idx vs) w)

  %hide B.getBits8

  lengthReplaceAt :
    (idx : Nat) -> (val : a) -> (vs : List a) ->
    {auto 0 bnds : InBounds idx vs} ->
    length (replaceAt idx val vs) === length vs
  lengthReplaceAt _ val [] = void $ absurd bnds
  lengthReplaceAt 0 val (x :: xs) @{InFirst} = Refl
  lengthReplaceAt (S k) val (x :: xs) @{InLater bnds}
    = cong S (lengthReplaceAt k val xs)

  export %inline
  setBits8 :
    LinearIO io =>
    {start : Nat} ->
    (1 _ : Owned region start end vs) ->
    (idx : Nat) -> (0 _ : InBounds idx vs) ->
    (val : Bits8) ->
    L1 io (Owned region start end (replaceAt idx val vs))
  setBits8 (MkOwned region size) idx bnds v
    = do B.setBits8 (getBuffer region) (cast (start + cast idx)) v
         pure1 $ MkOwned region $ Calc $
           |~ start + length (replaceAt idx v vs)
           ~~ start + length vs
              ..>( cong (start +) (lengthReplaceAt idx v vs) )
           ~~ end
              ..>( size )

  %hide B.setBits8

0 Map : (Type -> Type) -> Type
Map io =
  forall region.
  {start, end : Nat} ->
  {0 vs : List Bits8} ->
  (f : Bits8 -> Bits8) ->
  Owned region start end vs -@
  L1 io (Owned region start end (map f vs))

mapChips :
  (f : a -> b) -> (sx : SnocList a) -> (xs : List a) ->
  map f (sx <>> xs) === (map f sx <>> map f xs)
mapChips f [<] xs = Refl
mapChips f (sx :< x) xs = mapChips f sx (x :: xs)

mkIndexChips : HasLength m pref -> InBounds n xs -> InBounds (m + n) (pref <>> xs)
mkIndexChips Z bnds = bnds
mkIndexChips (S hl) bnds
  = rewrite plusSuccRightSucc (pred m) n in
    mkIndexChips hl (InLater bnds)

inBoundsUnique : (p, q : List.InBounds idx xs) -> p === q
inBoundsUnique InFirst InFirst = Refl
inBoundsUnique (InLater p) (InLater q)
  = cong InLater (inBoundsUnique p q)

replaceAtAppend :
  {0 acc, rest : List a} ->
  HasLength pref acc ->
  (bndsL : InBounds (pref + idx) (acc ++ rest)) ->
  (bndsR : InBounds idx rest) ->
  replaceAt (pref + idx) val (acc ++ rest) @{bndsL}
    === (acc ++ replaceAt idx val rest @{bndsR})
replaceAtAppend Z bndsL bndsR
  = cong (\ bnds => replaceAt idx val rest @{bnds})
  $ inBoundsUnique bndsL bndsR
replaceAtAppend {acc = x :: xs} (S hl) (InLater bndsL) bndsR
  = cong (x ::) (replaceAtAppend hl bndsL bndsR)

replaceAtChips :
  HasLength m acc ->
  midx === m + idx ->
  (bndsL : InBounds midx (acc <>> rest)) ->
  (bndsR : InBounds idx rest) ->
  replaceAt midx val (acc <>> rest) @{bndsL}
    === (acc <>> replaceAt idx val rest @{bndsR})
replaceAtChips Z Refl bndsL bndsR
  = rewrite inBoundsUnique bndsL bndsR in Refl
replaceAtChips (S {sa = acc} {a} hl) eq bndsL bndsR
  = replaceAtChips hl
      (trans eq (plusSuccRightSucc (pred m) idx))
      bndsL
      (InLater bndsR)

indexChips :
  HasLength m acc ->
  midx === m + idx ->
  (bndsL : InBounds midx (acc <>> rest)) ->
  (bndsR : InBounds idx rest) ->
  index midx (acc <>> rest) @{bndsL} === index idx rest @{bndsR}
indexChips Z Refl bndsL bndsR
  = rewrite inBoundsUnique bndsL bndsR in Refl
indexChips (S hl) eq bndsL bndsR
  = indexChips hl (trans eq (plusSuccRightSucc (pred m) idx)) bndsL (InLater bndsR)

export
map : LinearIO io => Map io
map f (MkOwned region eq)
  = let buf = MkOwned region eq in loop Z (view _ (hasLength buf)) buf where

  loop :
    {idx : Nat} -> {0 acc : SnocList Bits8} -> (0 _ : HasLength idx acc) ->
    {0 m : Nat} -> {0 rest : List Bits8} -> {0 hl : HasLength m rest} ->
    View rest m hl ->
    (1 _ : Owned region start end (map f acc <>> rest)) ->
    L1 io (Owned region start end (map f (acc <>> rest)))
  loop hl Z buf
    = pure1 $ reindex (sym $ mapChips f acc []) buf
  loop hl (S {x = v} rsize hlrest) buf
    = do let 0 bnds :=
               rewrite sym $ plusZeroRightNeutral idx in
               mkIndexChips (map f hl) InFirst
         buf # val <- getBits8 buf idx bnds
         let 0 fhl := map f hl
         let 0 eq : idx === idx + 0 := sym $ plusZeroRightNeutral idx
         let Val v = the (Singleton v) $ reindex (indexChips fhl eq bnds InFirst) val
         buf <- setBits8 buf idx bnds (f v)
         let 1 buf = reindex (replaceAtChips fhl eq bnds InFirst) buf
         loop (S hl) (view rsize hlrest) buf


0 mapConst : HasLength m vs -> (v : a) -> map (const v) vs === replicate m v
mapConst Z v = Refl
mapConst (S hl) v = cong (v ::) (mapConst hl v)

export
initialise :
  LinearIO io =>
  (v : Bits8) ->
  {start, end : Nat} ->
  {0 vs : List Bits8} ->
  Owned region start end vs -@
  L1 io (Owned region start end (replicate (minus end start) v))
initialise v buf = do
  let 0 hl = hasLength buf
  buf <- Indexed.map (const v) buf
  pure1 (reindex (mapConst hl v) buf)

public export
interface Monoid m => VerifiedMonoid (m : Type) where
  constructor MkVerifiedMonoid
  leftNeutral   : (x : m) -> Interfaces.neutral <+> x === x
  rightNeutral  : (x : m) -> x <+> Interfaces.neutral === x
  opAssociative : (x, y, z : m) -> x <+> (y <+> z) === (x <+> y) <+> z

export
[Additive] VerifiedMonoid Nat using Monoid.Additive where
  leftNeutral = plusZeroLeftNeutral
  rightNeutral = plusZeroRightNeutral
  opAssociative = plusAssociative

0 FoldMap : (Type -> Type) -> Type -> Type
FoldMap io m =
  VerifiedMonoid m => (f : Bits8 -> m) ->
  forall region.
  {start, end : Nat} ->
  {0 vs : List Bits8} ->
  Owned region start end vs -@
  L1 io (WithVal (Owned region start end vs)
                 (Singleton (foldMap f vs)))
foldlOpInit :
  VerifiedMonoid m =>
  (f : a -> m) ->
  (lval, rval : m) ->
  (xs : List a) ->
  foldl (\acc, v => acc <+> f v) (lval <+> rval) xs
  === lval <+> foldl (\acc, v => acc <+> f v) rval xs
foldlOpInit f lval rval [] = Refl
foldlOpInit f lval rval (x :: xs) = Calc $
  |~ foldl _ (lval <+> rval) (x :: xs)
  ~~ foldl _ (lval <+> rval <+> f x) xs
     ..>( Refl )
  ~~ foldl _ (lval <+> (rval <+> f x)) xs
     ..<( cong (\ v => foldl (\acc, v => acc <+> f v) v xs)
               (opAssociative lval rval (f x)) )
  ~~ lval <+> foldl _ (rval <+> f x) xs
     ..>( foldlOpInit f lval (rval <+> f x) xs )
  ~~ lval <+> foldl _ rval (x :: xs)
     ..>( Refl )

foldrOpInit :
  VerifiedMonoid m =>
  (f : a -> m) ->
  (lval, rval : m) ->
  (sx : SnocList a) ->
  foldr (\v, acc => f v <+> acc) (lval <+> rval) sx
  === foldr (\v, acc => f v <+> acc) lval sx <+> rval
foldrOpInit f lval rval [<] = Refl
foldrOpInit f lval rval (sx :< x) = Calc $
  |~ foldr _ (lval <+> rval) (sx :< x)
  ~~ foldr _ (f x <+> (lval <+> rval)) sx
     ..>( Refl )
  ~~ foldr _ ((f x <+> lval) <+> rval) sx
     ..>( cong (\ v => foldr (\v, acc => f v <+> acc) v sx)
               (opAssociative (f x) lval rval) )
  ~~ foldr _ (f x <+> lval) sx <+> rval
     ..>( foldrOpInit f (f x <+> lval) rval sx )
  ~~ foldr _ lval (sx :< x) <+> rval
     ..>( Refl )

foldMapCons : VerifiedMonoid m =>
  (f : a -> m) ->
  (x : a) -> (xs : List a) ->
  foldMap f (x :: xs) === f x <+> foldMap f xs
foldMapCons f x xs = Calc $
  |~ foldMap f (x :: xs)
  ~~ foldl _ neutral (x :: xs) ..>( Refl )
  ~~ foldl _ (neutral <+> f x) xs ..> ( Refl )
  ~~ foldl _ (f x) xs
     ..> ( cong (\ v => foldl (\ acc, v => acc <+> f v) v xs)
                (leftNeutral (f x)) )
  ~~ foldl _ (f x <+> neutral) xs
     ..< ( cong (\ v => foldl (\ acc, v => acc <+> f v) v xs)
                (rightNeutral (f x)) )
  ~~ f x <+> foldl _ neutral xs
     ..> ( foldlOpInit f (f x) neutral xs )
  ~~ f x <+> foldMap f xs ..> ( Refl )

foldMapAppend : VerifiedMonoid m =>
  (f : a -> m) ->
  (xs, ys : List a) ->
  foldMap f (xs ++ ys) === foldMap f xs <+> foldMap f ys
foldMapAppend f [] ys = sym $ leftNeutral (foldMap f ys)
foldMapAppend f (x :: xs) ys = Calc $
  |~ foldMap f (x :: xs ++ ys)
  ~~ f x <+> foldMap f (xs ++ ys)
     ..>( foldMapCons f x (xs ++ ys) )
  ~~ f x <+> (foldMap f xs <+> foldMap f ys)
     ..>( cong (f x <+>) (foldMapAppend f xs ys) )
  ~~ (f x <+> foldMap f xs) <+> foldMap f ys
     ..>( opAssociative (f x) (foldMap f xs) (foldMap f ys) )
  ~~ foldMap f (x :: xs) <+> foldMap f ys
     ..<( cong (<+> foldMap f ys) (foldMapCons f x xs) )

foldMapSnoc : VerifiedMonoid m =>
  (f : a -> m) ->
  (sx : SnocList a) -> (x : a) ->
  foldMap f (sx :< x) === foldMap f sx <+> f x
foldMapSnoc f sx x = Calc $
  |~ foldMap f (sx :< x)
  ~~ foldr _ neutral (sx :< x) ..>( Refl )
  ~~ foldr _ (f x <+> neutral) sx ..>( Refl )
  ~~ foldr _ (f x) sx
     ..>( cong (\ v => foldr (\ v, acc => f v <+> acc) v sx)
                (rightNeutral (f x)) )
  ~~ foldr _ (neutral <+> f x) sx
     ..<( cong (\ v => foldr (\ v, acc => f v <+> acc) v sx)
                (leftNeutral (f x)) )
  ~~ foldr _ neutral sx <+> f x
     ..>( foldrOpInit f neutral (f x) sx )
  ~~ foldMap f sx <+> f x ..>( Refl )

foldMapChips :
  VerifiedMonoid m =>
  (f : a -> m) -> (sx : SnocList a) -> (xs : List a) ->
  foldMap f (sx <>> xs) === foldMap f sx <+> foldMap f xs
foldMapChips f [<] xs = sym $ leftNeutral (foldMap f xs)
foldMapChips f (sx :< x) xs = Calc $
  |~ foldMap f (sx :< x <>> xs)
  ~~ foldMap f (sx <>> x :: xs)
     ..>( Refl )
  ~~ foldMap f sx <+> foldMap f (x :: xs)
     ..>( foldMapChips f sx (x :: xs) )
  ~~ foldMap f sx <+> (f x <+> foldMap f xs)
     ..>( cong (foldMap f sx <+>) (foldMapCons f x xs) )
  ~~ (foldMap f sx <+> f x) <+> foldMap f xs
     ..>( opAssociative (foldMap f sx) (f x) (foldMap f xs) )
  ~~ foldMap f (sx :< x) <+> foldMap f xs
     ..<( cong (<+> foldMap f xs) (foldMapSnoc f sx x) )

foldMapCast :
  VerifiedMonoid m =>
  (f : a -> m) -> (sx : SnocList a) ->
  foldMap f sx === foldMap f (sx <>> [])
foldMapCast f sx = Calc $
  |~ foldMap f sx
  ~~ foldMap f sx <+> neutral      ..<( rightNeutral (foldMap f sx) )
  ~~ foldMap f sx <+> foldMap f [] ..<( Refl )
  ~~ foldMap f (sx <>> [])         ..<( foldMapChips f sx [] )

foldMap : LinearIO io => FoldMap io m
foldMap f (MkOwned region eq)
  = let buf = MkOwned region eq in
    loop Z (view _ (hasLength buf)) buf (pure neutral) where

  loop :
    {idx : Nat} -> {0 acc : SnocList Bits8} -> (0 _ : HasLength idx acc) ->
    {0 m : Nat} -> {0 rest : List Bits8} -> {0 hl : HasLength m rest} ->
    View rest m hl ->
    (1 _ : Owned region start end (acc <>> rest)) ->
    Singleton (foldMap f acc) ->
    L1 io (WithVal (Owned region start end (acc <>> rest))
                   (Singleton (foldMap f (acc <>> rest))))
  loop hl Z buf val
    = pure1 (buf # reindex (foldMapCast f acc) val)
  loop hl (S {x = v} rsize hlrest) buf val
    = do let 0 bnds :=
               rewrite sym $ plusZeroRightNeutral idx in
               mkIndexChips hl InFirst
         buf # got <- getBits8 buf idx bnds
         let 0 eq : idx === idx + 0 := sym $ plusZeroRightNeutral idx
         let got = reindex (indexChips hl eq bnds InFirst) got
         loop (S hl) (view rsize hlrest) buf
           $ reindex (sym $ foldMapSnoc f acc v) [| val <+> [| f got |] |]

namespace Sum

  %hint
  additive : VerifiedMonoid Nat
  additive = Additive

  public export
  0 Sum : (Type -> Type) -> Type
  Sum io =
    forall region.
    {start, end : Nat} ->
    forall vs.
    Owned region start end vs -@
    L1 io (WithVal (Owned region start end vs) (Singleton (foldMap {m = Nat} Prelude.cast vs)))

  export
  sum : LinearIO io => Sum io
  sum = foldMap {m = Nat} cast

div2 : (n : Nat) -> (m ** p ** m + p === n)
div2 n =
  -- This is unsafe just so that we can get a fast division by two...
  let i   : Integer = cast n in                 -- n
  let i0  : Bool = testBit i 0 in               -- i[0]
  let i2  : Integer = i `shiftR` 1 in           -- n / 2
  let ln2 : Nat = cast i2 in                    -- ⌊ n / 2 ⌋
  let un2 : Nat = ifThenElse i0 (S ln2) ln2 in  -- ⌈ n / 2 ⌉
  -- postulate correctness as we currently cannot prove it
  let 0 correct : ln2 + un2 === n in            -- ⌊ n / 2 ⌋ + ⌈ n / 2 ⌉ === n
  (ln2 ** un2 ** irrelevantEq correct)

0 takeDropSplit : (m : Nat) -> (vs : List a) ->
  (take m vs ++ drop m vs) === vs
takeDropSplit 0 vs = Refl
takeDropSplit (S m) [] = Refl
takeDropSplit (S m) (v :: vs) = cong (v ::) (takeDropSplit m vs)

0 mapTake : (f : a -> b) -> (m : Nat) -> (vs : List a) ->
  map f (take m vs) === take m (map f vs)
mapTake f 0 vs = Refl
mapTake f (S m) [] = Refl
mapTake f (S m) (v :: vs) = cong (f v ::) (mapTake f m vs)

0 mapDrop : (f : a -> b) -> (m : Nat) -> (vs : List a) ->
  map f (drop m vs) === drop m (map f vs)
mapDrop f 0 vs = Refl
mapDrop f (S m) [] = Refl
mapDrop f (S m) (v :: vs) = mapDrop f m vs

nonpar : L1 IO a -@ L1 IO b -@ L1 IO (LPair a b)
nonpar x y = do
  vx <- x
  vy <- y
  pure1 (vx # vy)

takeHasLength :
  {m : Nat} -> {vs : List Bits8} ->
  HasLength (m + p) vs -> HasLength m (take m vs)
takeHasLength {m = 0} hl = Z
takeHasLength {m = S m} (S hl) = S (takeHasLength hl)

halve :
  {start, end : Nat} ->
  (1 _ : Owned region start end vs) ->
  Res Nat (\ m =>
  LPair (Owned region start       (start + m) (take m vs))
        (Owned region (start + m) end         (drop m vs)))
halve buf = do
  let 1 res = length buf
  let Element n hl # buf = res
  let (m ** p ** Refl) = div2 n
  let 1 buf = reindex (sym $ takeDropSplit m vs) buf
  m # splitAt (takeHasLength hl) buf

mapTakeDrop :
  (f : a -> b) -> (m : Nat) -> (vs : List a) ->
  map f (take m vs) ++ map f (drop m vs) === map f vs
mapTakeDrop f m vs =
  trans
    (cong2 (++) (mapTake f m vs) (mapDrop f m vs))
    (takeDropSplit m (map f vs))

parMapRec : Map IO -> Map IO
parMapRec subMap saw buf
   = do let (m # lbuf # rbuf) = halve buf
        (lbuf # rbuf) <- par1 (subMap saw lbuf) (subMap saw rbuf)
        let 1 buf = lbuf ++ rbuf
        pure1 (reindex (mapTakeDrop saw m vs) buf)

parFoldMapRec : FoldMap IO m -> FoldMap IO m
parFoldMapRec subFoldMap f buf
   = do let 1 res = length buf
        let Element n hl # buf = res
        let (m ** p ** Refl) = div2 n
        let 1 buf = reindex (sym $ takeDropSplit m vs) buf
        let 1 buf = splitAt (takeHasLength hl) buf
        let lbuf # rbuf = buf
        res <- par1 (subFoldMap f lbuf) (subFoldMap f rbuf)
        let (lbuf # lres) # (rbuf # rres) = res
        let 1 buf = lbuf ++ rbuf
        let 0 eq : foldMap f (take m vs) <+> foldMap f (drop m vs) === foldMap f vs
          := trans (sym $ foldMapAppend f (take m vs) (drop m vs))
                   (cong (foldMap f) (takeDropSplit m vs))
        pure1 $ reindex (takeDropSplit m vs) buf
              # reindex eq [| lres <+> rres |]

export
iterate : Nat -> (a -> a) -> (a -> a)
iterate 0 f x = x
iterate (S k) f x = f (iterate k f x)

export
parMap : Nat -> Map IO
parMap n = iterate n parMapRec map

export
parFoldMap : Nat -> FoldMap IO m
parFoldMap n = iterate n parFoldMapRec (foldMap @{%search} @{_})

measure : LinearIO io => String -> L1 io () -@ L1 io ()
measure str act = do
  start <- liftIO $ clockTime Monotonic
  act
  end <- liftIO $ clockTime Monotonic
  let time = timeDifference end start
  let stime = showTime 2 9
  putStrLn "Time \{str}: \{stime time}"
  pure1 ()


export
experiment : LinearIO io => String -> Nat -> Map io -> FoldMap io Nat -> L io ()
experiment str n theMap theFold = do
  Just (MkDynBuffer buf) <- allocate n
    | Nothing => die "Oops couldn't allocate the buffer for test \{str}"
  measure str $ do
    putStrLn "Mapping..."
    buf <- theMap (const 2) buf
    putStrLn "Summing..."
    buf # val <- theFold @{Additive} cast buf
    printLn val.unVal
    pure1 (free buf)
  pure ()

export
main : IO ()
main = LIO.run $ do
  let n = 100_000_000
--  experiment "sequential" n map
  for_ [3..4] $ \ splits =>
    experiment "parallel (2^\{show splits} threads)" n (parMap splits) (parFoldMap splits)
