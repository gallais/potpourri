module Indexed

import Data.Fin
import Data.DPair
import Data.List
import Data.Vect
import Data.Buffer
import System.File.Buffer

%default total

namespace Tuple

  ||| A description is a nested tuple of Bytes or recursive positions
  ||| It is indexed by:
  |||  @size      the statically known part of the size (in number of bytes)
  |||  @offsets   the dynamically known part of the size (in number of subtrees)
  |||  @rightmost telling us whether we are in the rightmost subterm
  |||             in which case `Rec` won't need to record an additional offset
  public export
  data Desc : (size : Nat) -> (offsets : Nat) -> (rightmost : Bool) -> Type where
    None : Desc 0 0 b
    Byte : Desc 1 0 b
    Prod : {sl, sr, m, n : Nat} -> -- does not matter: Descs are meant to go away with staging
           (d : Desc sl m False) ->
           (e : Desc sr n b) ->
           Desc (sl + sr) (m + n) b
    Rec : Desc 0 (ifThenElse b 0 1) b

  ||| Meaning where subterms are interpreted using the parameter
  public export
  Meaning : Desc s n b -> Type -> Type
  Meaning None x = ()
  Meaning Byte x = Bits8
  Meaning (Prod d e) x = (Meaning d x, Meaning e x)
  Meaning Rec x = x

  public export
  Meaning' : Desc s n b -> Type -> Type -> Type
  Meaning' None x r = r
  Meaning' Byte x r = Bits8 -> r
  Meaning' (Prod d e) x r = Meaning' d x (Meaning' e x r)
  Meaning' Rec x r = x -> r

  public export
  curry : (d : Desc s n b) -> (Meaning d x -> r) -> Meaning' d x r
  curry None k = k ()
  curry Byte k = k
  curry (Prod d e) k = curry d (curry e . curry k)
  curry Rec k = k

namespace Data

  ||| A constructor description is essentially an existential type
  ||| around a description
  public export
  record Constructor where
    constructor MkConstructor
    {size : Nat}
    {offsets : Nat}
    description : Desc size offsets True

  ||| A data description is a sum over a list of constructor types
  public export
  Data : Type
  Data = List Constructor

  data Lookup : (xs : List a) -> (k : Nat) -> a -> Type where
    [search xs k, uniqueSearch]
    Z : Lookup (x :: xs) 0 x
    S : Lookup xs k x -> Lookup (_ :: xs) (S k) x

  namespace Singleton

    public export
    data Singleton : a -> Type where
      MkSingleton : (x : a) -> Singleton x

    public export
    getSingleton : Singleton {a} x -> a
    getSingleton (MkSingleton x) = x

    export
    lookup : {xs : List a} -> {k : Nat} -> (0 prf : Lookup xs k x) -> Singleton x
    lookup {xs = x :: xs} {k = 0} Z = MkSingleton x
    lookup {xs = x :: xs} {k = S k} (S prf) = lookup prf

  namespace Tentative

    export
    lookup : (xs : List a) -> (k : Nat) -> Maybe (Subset a (Lookup xs k))
    lookup [] k = Nothing
    lookup (x :: xs) 0 = Nothing
    lookup (x :: xs) (S k) = bimap id S <$> lookup xs k

  ||| Fixpoint of the description:
  ||| 1. pick a constructor
  ||| 2. give its meaning where subterms are entire subtrees
  covering
  data Mu : Data -> Type where
    MkMu : (k : Fin (length cs)) ->
           Meaning (description (index' cs k)) (Mu cs) ->
           Mu cs

  mkMu : (cs : Data) -> (k : Fin (length cs)) ->
         Meaning' (description (index' cs k)) (Mu cs) (Mu cs)
  mkMu cs k = curry (description (index' cs k)) (MkMu k)

  parameters {cs : Data} (buf : Buffer)

    setInts : Int -> Vect n Int -> IO ()
    setInts start [] = pure ()
    setInts start (i :: is)
      = do setInt buf start i
           setInts (start + 8) is

    muToBuffer : Int -> Mu cs -> IO Int
    elemToBuffer :
      Int ->
      {b : Bool} -> (d : Desc s n b) ->
      Meaning d (Mu cs) ->
      IO (Vect n Int, Int)

    muToBuffer start (MkMu k t) with (index' cs k)
      _ | cons
        = do -- [ Tag | ... offsets ... | t1 | t2 | ... ]
             setBits8 buf start (cast $ cast {to = Nat} k)
             let afterTag  = start + 1
             let afterOffs = afterTag + 8 * cast (offsets cons)
             (is, end) <- elemToBuffer afterOffs (description cons) t
             setInts afterTag is
             pure end

    elemToBuffer start None v = pure ([], start)
    elemToBuffer start Byte v = ([], start + 1) <$ setBits8 buf start v
    elemToBuffer start (Prod d e) (v, w)
      = do (n1, afterLeft) <- elemToBuffer start d v
           (n2, afterRight) <- elemToBuffer afterLeft e w
           pure (n1 ++ n2, afterRight)
    elemToBuffer start {b} Rec v
      = do end <- muToBuffer start v
           pure $ (,end) $ if b then [] else [end - start]

  writeToFile : {cs : Data} -> String -> Mu cs -> IO ()
  writeToFile fp mu = do
    Just buf <- newBuffer 655360
      | Nothing => assert_total (idris_crash "Couldn't allocate buffer")
    size <- muToBuffer buf 0 mu
    Right () <- writeBufferToFile fp buf size
      | Left (err, _) => assert_total (idris_crash (show err))
    pure ()

namespace Pointer

  record Elem (d : Desc s n b) (cs : Data) (0 t : Meaning d (Data.Mu cs)) where
    constructor MkElem
    subterms : Vect n Int
    elemBuffer : Buffer
    elemPosition : Int

  record Mu (cs : Data) (t : Data.Mu cs) where
    constructor MkMu
    muBuffer : Buffer
    muPosition : Int

  Poke : (d : Desc s n b) -> (cs : Data) -> Meaning d (Data.Mu cs) -> Type
  Poke None _ t = ()
  Poke Byte cs t = Bits8
  Poke (Prod d e) cs t = (Elem d cs (fst t), Elem e cs (snd t))
  Poke Rec cs t = Pointer.Mu cs t

  poke : {s : Nat} -> (d : Desc s n b) ->
         forall t. Elem d cs t -> IO (Poke d cs t)
  poke None el = pure ()
  poke Byte el = getBits8 (elemBuffer el) (elemPosition el)
  poke (Prod {sl} d e) el = do
    let (n1, n2) = splitAt _ (subterms el)
    let left = MkElem n1 (elemBuffer el) (elemPosition el)
    let pos = elemPosition el + sum n1 + cast sl
    let right = MkElem n2 (elemBuffer el) pos
    pure (left, right)
  poke Rec el = pure (MkMu (elemBuffer el) (elemPosition el))

  data Layer : (d : Desc s n b) -> (cs : Data) -> Meaning d (Data.Mu cs) -> Type where
    MkUnit : Layer None cs t
    MkVal  : Bits8 -> Layer Byte cs t
    MkPair : Layer d cs t -> Layer e cs u -> Layer (Prod d e) cs (t, u)
    Box    : Pointer.Mu cs t -> Layer Rec cs t

  etaPair : (p : (a, b)) -> p === (fst p, snd p)
  etaPair (t, u) = Refl

  layer : {s : Nat} -> (d : Desc s n b) ->
          forall t. Elem d cs t -> IO (Layer d cs t)
  layer d el = poke d el >>= go d where

    go : forall n, b. {s : Nat} -> (d : Desc s n b) ->
         forall t. Poke d cs t -> IO (Layer d cs t)
    go None p = pure MkUnit
    go Byte p = pure (MkVal p)
    go (Prod d e) {t} (p, q) = rewrite etaPair t in MkPair <$> layer d p <*> layer e q
    go Rec p = pure (Box p)

  data Out : (cs : Data) -> (t : Data.Mu cs) -> Type where
    MkOut : (k : (Fin (length cs))) ->
            forall t. Elem (description (index' cs k)) cs t ->
            Out cs (MkMu k t)

  -- postulated, utterly unsafe
  0 unfoldAs :
    (k : Fin (length cs)) -> (t : Data.Mu cs) ->
    (val : Meaning (description (index' cs k)) (Data.Mu cs) ** t === MkMu k val)

  out : {cs : _} -> forall t. Pointer.Mu cs t -> IO (Out cs t)
  out {t} mu = do
    tag <- getBits8 (muBuffer mu) (muPosition mu)
    let Just k = natToFin (cast tag) (length cs)
      | _ => assert_total (idris_crash "Invalid representation")
    let 0 sub = unfoldAs k t
    val <- MkOut k <$> getConstructor k {t = sub.fst} (rewrite sym sub.snd in mu)
    pure (rewrite sub.snd in val)

    where

    getOffsets : Buffer -> Int -> -- Buffer & position
                 (n : Nat) ->
                 forall t. (Vect n Int -> Int -> Elem d cs t) ->
                 IO (Elem d cs t)
    getOffsets buf pos 0 k = pure (k [] pos)
    getOffsets buf pos (S n) k = do
      off <- getInt buf pos
      getOffsets buf (8 + pos) n (k . (off ::))

    getConstructor :
      (k : Fin (length cs)) ->
      forall t.
      Pointer.Mu cs (MkMu k t) ->
      IO (Elem (description (index' cs k)) cs t)
    getConstructor k mu
      = getOffsets (muBuffer mu) (1 + muPosition mu) (offsets (index' cs k))
      $ \ subterms, pos => MkElem subterms (muBuffer mu) pos

Tree : Data
Tree = [ MkConstructor None                       -- Leaf
       , MkConstructor (Prod Rec (Prod Byte Rec)) -- Node Tree Bits8 Tree
       ]

ATree : Type
ATree = Data.Mu Tree

leaf : ATree
leaf = mkMu Tree 0

node : ATree -> Bits8 -> ATree -> ATree
node = mkMu Tree 1

example : ATree
example
  = node
      (node (node leaf 1 leaf) 5 leaf)
      10
      (node leaf 20 leaf)

sum : Pointer.Mu Tree t -> IO Nat
sum t = case !(out t) of
  MkOut 0 el => pure 0
  MkOut 1 el => do
    (MkPair (Box l) (MkPair (MkVal b) (Box r))) <- layer _ el
    pure (!(sum l) + cast b + !(sum r))

init : (cs : Data) -> Buffer -> IO (Exists (Pointer.Mu cs))
init cs buf = pure (Evidence t (MkMu buf 0)) where 0 t : Mu cs

main : IO ()
main = do
  writeToFile "tmp" example
  Right buf <- createBufferFromFile "tmp"
    | Left err => assert_total (idris_crash (show err))
  Evidence _ tree <- init Tree buf
  val <- sum tree
  putStrLn "Sum: \{show val}"
