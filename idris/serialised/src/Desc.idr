module Desc

import Data.Fin
import Data.Vect
import Data.List
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

  ||| Fixpoint of the description:
  ||| 1. pick a constructor
  ||| 2. give its meaning where subterms are entire subtrees
  covering
  data Mu : Data -> Type where
    MkMu : (k : Fin (length cs)) ->
           Meaning (description $ index' cs k) (Mu cs) ->
           Mu cs

  mkMu : (cs : Data) -> (k : Fin (length cs)) -> Meaning' (description $ index' cs k) (Mu cs) (Mu cs)
  mkMu cs k = curry (description $ index' cs k) (MkMu k)

  parameters {ds : Data} (buf : Buffer)

    setInts : Int -> Vect n Int -> IO ()
    setInts start [] = pure ()
    setInts start (i :: is)
      = do setInt buf start i
           setInts (start + 8) is

    muToBuffer : Int -> Mu ds -> IO Int
    elemToBuffer :
      Int ->
      {b : Bool} -> (d : Desc s n b) ->
      Meaning d (Mu ds) ->
      IO (Vect n Int, Int)

    muToBuffer start (MkMu k t) with (index' ds k)
      _ | cons = do -- [ Tag | ... offsets ... | t1 | t2 | ... ]
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

  writeToFile : {ds : Data} -> String -> Mu ds -> IO ()
  writeToFile fp mu = do
    Just buf <- newBuffer 655360
      | Nothing => assert_total (idris_crash "Couldn't allocate buffer")
    size <- muToBuffer buf 0 mu
    Right () <- writeBufferToFile fp buf size
      | Left (err, _) => assert_total (idris_crash (show err))
    pure ()

namespace Pointer

  record Elem (d : Desc s n b) (cs : Data) where
    constructor MkElem
    subterms : Vect n Int
    elemBuffer : Buffer
    elemPosition : Int

  record Mu (cs : Data) where
    constructor MkMu
    muBuffer : Buffer
    muPosition : Int

  Poke : (d : Desc s n b) -> (cs : Data) -> Type
  Poke None _ = ()
  Poke Byte cs = Bits8
  Poke (Prod d e) cs = (Elem d cs, Elem e cs)
  Poke Rec cs = Pointer.Mu cs

  poke : {s : Nat} -> (d : Desc s n b) -> Elem d cs -> IO (Poke d cs)
  poke None el = pure ()
  poke Byte el = getBits8 (elemBuffer el) (elemPosition el)
  poke (Prod {sl} d e) el = do
    let (n1, n2) = splitAt _ (subterms el)
    let left = MkElem n1 (elemBuffer el) (elemPosition el)
    let pos = elemPosition el + sum n1 + cast sl
    let right = MkElem n2 (elemBuffer el) pos
    pure (left, right)
  poke Rec el = pure (MkMu (elemBuffer el) (elemPosition el))

  Layer : (d : Desc s n b) -> (cs : Data) -> Type
  Layer None cs = ()
  Layer Byte cs = Bits8
  Layer (Prod d e) cs = (Layer d cs, Layer e cs)
  Layer Rec cs = Pointer.Mu cs

  layer : {s : Nat} -> (d : Desc s n b) -> Elem d cs -> IO (Layer d cs)
  layer d el = poke d el >>= go d where

    go : forall n, b. {s : Nat} -> (d : Desc s n b) -> Poke d cs -> IO (Layer d cs)
    go None p = pure p
    go Byte p = pure p
    go (Prod d e) (p, q) = [| (layer d p, layer e q) |]
    go Rec p = pure p

  record Out (cs : Data) where
    constructor MkOut
    choice : Fin (length cs)
    encoding : Elem (description $ index' cs choice) cs

  out : {cs : _} -> Pointer.Mu cs -> IO (Out cs)
  out mu = do
    tag <- getBits8 (muBuffer mu) (muPosition mu)
    let Just choice = natToFin (cast tag) (length cs)
      | _ => assert_total (idris_crash "Invalid representation")
    MkOut choice <$> getConstructor (index' cs choice) mu

    where

    getOffsets : Buffer -> Int -> -- Buffer & position
                 (n : Nat) ->
                 (Vect n Int -> Int -> Elem d cs) ->
                 IO (Elem d cs)
    getOffsets buf pos 0 k = pure (k [] pos)
    getOffsets buf pos (S n) k = do
      off <- getInt buf pos
      getOffsets buf (8 + pos) n (k . (off ::))

    getConstructor : (c : Constructor) -> Pointer.Mu cs -> IO (Elem (description c) cs)
    getConstructor c mu
      = getOffsets (muBuffer mu) (1 + muPosition mu) (offsets c)
      $ \ subterms, pos => MkElem subterms (muBuffer mu) pos


Tree : Data
Tree = [ MkConstructor None                       -- Leaf
       , MkConstructor (Prod Rec (Prod Byte Rec)) -- Node Tree Bits8 Tree
       ]

example : Data.Mu Tree
example
  = mkMu Tree 1
      (mkMu Tree 0)
      10
      (mkMu Tree 1
         (mkMu Tree 0)
         20
         (mkMu Tree 0))

sum : Pointer.Mu Tree -> IO Nat
sum t = case !(out t) of
  MkOut 0 el => pure 0
  MkOut 1 el => do
    (l, b, r) <- layer _ el
    m <- assert_total (sum l)
    n <- assert_total (sum r)
    pure (m + n + cast b)

main : IO ()
main = do
  writeToFile "tmp" example
  Right buf <- createBufferFromFile "tmp"
    | Left err => assert_total (idris_crash (show err))
  let tree : Pointer.Mu Tree = MkMu buf 0
  val <- sum tree
  putStrLn "Sum: \{show val}"
