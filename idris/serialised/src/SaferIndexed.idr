module SaferIndexed

import Data.Fin
import Data.DPair
import Data.List
import Data.Vect
import Data.Buffer
import System.File.Buffer

import Decidable.Equality

import Data.String
import Data.Singleton

%default total

failWith : String -> a
failWith str = assert_total (idris_crash str)

namespace Desc

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

  export
  Show (Desc s n b) where
    showPrec _ None = "()"
    showPrec _ Byte = "Bits8"
    showPrec p (Prod d e) =
      showParens (p <= Open) $ showPrec Open d ++ " * " ++ showPrec App e
    showPrec _ Rec = "X"

  ||| Heterogeneous equality check for descriptions
  eqDesc : Desc s n b -> Desc s' n' b' -> Bool
  eqDesc None None = True
  eqDesc Byte Byte = True
  eqDesc (Prod d e) (Prod s t) = eqDesc d s && eqDesc e t
  eqDesc Rec Rec = True
  eqDesc _ _ = False

  ||| A constructor description is essentially an existential type
  ||| around a description
  public export
  record Constructor where
    constructor MkConstructor
    {size : Nat}
    {offsets : Nat}
    description : Desc size offsets True

  export
  Eq Constructor where
    MkConstructor d == MkConstructor e = eqDesc d e

  ||| A data description is a sum over a list of constructor types
  public export
  Data : Type
  Data = List Constructor

  export
  showData : Data -> String
  showData [] = "⊥"
  showData (c :: cs) = unlines
    $  ("μX. " ++ show (description c))
    :: (("  + " ++) <$> map (\ c => show (description c)) cs)

  parameters (buf : Buffer)

    setDesc : Int -> Desc s n b -> IO Int
    setDesc start None = (start + 1) <$ setBits8 buf start 0
    setDesc start Byte = (start + 1) <$ setBits8 buf start 1
    setDesc start (Prod d e)
      = do setBits8 buf start 2
           afterLeft <- setDesc (start + 1) d
           setDesc afterLeft e
    setDesc start Rec = (start + 1) <$ setBits8 buf start 3

    setConstructors : Int -> List Constructor -> IO Int
    setConstructors start [] = pure start
    setConstructors start (MkConstructor d :: cs)
      = do afterC <- setDesc start d
           setConstructors afterC cs

    export
    setData : Int -> Data -> IO Int
    setData start cs = do
      setBits8 buf start (cast $ length cs)
      setConstructors (start + 1) cs

    record IDesc (b : Bool) where
      constructor MkIDesc
      {size : Nat}
      {offsets : Nat}
      runIDesc : Desc size offsets b

    IProd : IDesc False -> IDesc b -> IDesc b
    IProd (MkIDesc d) (MkIDesc e) = MkIDesc (Prod d e)

    getDesc : {b : Bool} -> Int -> IO (Int, IDesc b)
    getDesc start = case !(getBits8 buf start) of
      0 => pure (start + 1, MkIDesc None)
      1 => pure (start + 1, MkIDesc Byte)
      2 => do (afterLeft, d) <- assert_total (getDesc {b = False} (start + 1))
              (end, e) <- assert_total (getDesc {b} afterLeft)
              pure (end, IProd d e)
      3 => pure (start + 1, MkIDesc Rec)
      _ => failWith "Invalid Description"

    getConstructors : Int -> Nat -> IO (List Constructor)
    getConstructors start 0 = pure []
    getConstructors start (S n)
      = do (afterD, d) <- getDesc start
           cs <- getConstructors afterD n
           pure (MkConstructor (runIDesc d) :: cs)

    export
    getData : Int -> IO Data
    getData start = do
      n <- getBits8 buf start
      let Just n = ifThenElse (n < 0) Nothing (Just (cast n))
         | Nothing => failWith "Invalid header"
      getConstructors (start + 1) n

namespace Data

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

  public export
  fmap : {d : Desc{}} -> (a -> b) -> Meaning d a -> Meaning d b
  fmap {d = None} f v = v
  fmap {d = Byte} f v = v
  fmap {d = Prod d e} f (v, w) = (fmap f v, fmap f w)
  fmap {d = Rec} f v = f v

  ||| Fixpoint of the description:
  ||| 1. pick a constructor
  ||| 2. give its meaning where subterms are entire subtrees
  public export covering
  data Mu : Data -> Type where
    MkMu : (k : Fin (length cs)) ->
           Meaning (description (index' cs k)) (Mu cs) ->
           Mu cs

  export
  mkMu : (cs : Data) -> (k : Fin (length cs)) ->
         Meaning' (description (index' cs k)) (Mu cs) (Mu cs)
  mkMu cs k = curry (description (index' cs k)) (MkMu k)

  public export
  fold : {cs : Data} ->
         (alg : (k : Fin (length cs)) -> Meaning (description (index' cs k)) a -> a) ->
         (t : Mu cs) -> a
  fold alg (MkMu k t) = alg k (assert_total $ fmap (fold alg) t)

  parameters {cs : Data} (buf : Buffer)

    setInts : Int -> Vect n Int -> IO ()
    setInts start [] = pure ()
    setInts start (i :: is)
      = do setInt buf start i
           setInts (start + 8) is

    setMu : Int -> Mu cs -> IO Int
    setMeaning :
      Int ->
      {b : Bool} -> (d : Desc s n b) ->
      Meaning d (Mu cs) ->
      IO (Vect n Int, Int)

    setMu start (MkMu k t) with (index' cs k)
      _ | cons
        = do -- [ Tag | ... offsets ... | t1 | t2 | ... ]
             setBits8 buf start (cast $ cast {to = Nat} k)
             let afterTag  = start + 1
             let afterOffs = afterTag + 8 * cast (offsets cons)
             (is, end) <- setMeaning afterOffs (description cons) t
             setInts afterTag is
             pure end

    setMeaning start None v = pure ([], start)
    setMeaning start Byte v = ([], start + 1) <$ setBits8 buf start v
    setMeaning start (Prod d e) (v, w)
      = do (n1, afterLeft) <- setMeaning start d v
           (n2, afterRight) <- setMeaning afterLeft e w
           pure (n1 ++ n2, afterRight)
    setMeaning start {b} Rec v
      = do end <- setMu start v
           pure $ (,end) $ if b then [] else [end - start]

  export
  writeToFile : {cs : Data} -> String -> Mu cs -> IO ()
  writeToFile fp mu = do
    Just buf <- newBuffer 655360
      | Nothing => failWith "Couldn't allocate buffer"
    end <- setData buf 8 cs
    setInt buf 0 (end - 8)
    size <- setMu buf end mu
    Right () <- writeBufferToFile fp buf size
      | Left (err, _) => failWith (show err)
    pure ()

namespace Pointer

  record Elem (d : Desc s n b) (cs : Data) (t : Meaning d (Data.Mu cs)) where
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
  Poke Byte cs t = Singleton t
  Poke (Prod d e) cs t = (Elem d cs (fst t), Elem e cs (snd t))
  Poke Rec cs t = Pointer.Mu cs t

  poke : {s : Nat} -> (d : Desc s n b) ->
         forall t. Elem d cs t -> IO (Poke d cs t)
  poke None el = pure ()
  poke Byte el = do
    bs <- getBits8 (elemBuffer el) (elemPosition el)
    pure (believe_me $ MkSingleton bs)
  poke (Prod {sl} d e) el = do
    let (n1, n2) = splitAt _ (subterms el)
    let left = MkElem n1 (elemBuffer el) (elemPosition el)
    let pos = elemPosition el + sum n1 + cast sl
    let right = MkElem n2 (elemBuffer el) pos
    pure (left, right)
  poke Rec el = pure (MkMu (elemBuffer el) (elemPosition el))

  etaPair : (p : (a, b)) -> p === (fst p, snd p)
  etaPair (t, u) = Refl

  data Layer' : (d : Desc s n b) -> (cs : Data) -> Meaning d (Data.Mu cs) -> Type

  Layer : (d : Desc s n b) -> (cs : Data) -> Meaning d (Data.Mu cs) -> Type
  Layer d@(Prod _ _) cs t = Layer' d cs t
  Layer None _ _ = ()
  Layer Byte _ t = Singleton t
  Layer Rec cs t = Pointer.Mu cs t


  data Layer' : (d : Desc s n b) -> (cs : Data) -> Meaning d (Data.Mu cs) -> Type where
    (#) : Layer d cs t -> Layer e cs u -> Layer' (Prod d e) cs (t, u)

  layer : {s : Nat} -> {d : Desc s n b} ->
          forall t. Elem d cs t -> IO (Layer d cs t)
  layer el = poke d el >>= go d where

    go : forall n, b. {s : Nat} -> (d : Desc s n b) ->
         forall t. Poke d cs t -> IO (Layer d cs t)
    go None p = pure ()
    go Byte p = pure p
    go (Prod d e) {t} (p, q) = rewrite etaPair t in [| layer p # layer q |]
    go Rec p = pure p

  data Out : (cs : Data) -> (t : Data.Mu cs) -> Type where
    MkOut : (k : (Fin (length cs))) ->
            forall t. Elem (description (index' cs k)) cs t ->
            Out cs (MkMu k t)

  out : {cs : _} -> forall t. Pointer.Mu cs t -> IO (Out cs t)
  out {t} mu = do
    tag <- getBits8 (muBuffer mu) (muPosition mu)
    let Just k = natToFin (cast tag) (length cs)
      | _ => failWith "Invalid representation"
    let 0 sub = unfoldAs k t
    val <- MkOut k <$> getConstructor k {t = sub.fst} (rewrite sym sub.snd in mu)
    pure (rewrite sub.snd in val)

    where

    -- postulated, utterly unsafe
    0 unfoldAs :
      (k : Fin (length cs)) -> (t : Data.Mu cs) ->
      (val : Meaning (description (index' cs k)) (Data.Mu cs)
       ** t === MkMu k val)
    {-
    unfoldAs k (MkMu l@_ val) with (decEq k l)
      _ | Yes Refl = (val ** Refl)
      _ | No _ = failWith "The IMPOSSIBLE has happened"
    -}

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

||| Raw sum
rsum : Pointer.Mu Tree t -> IO Nat
rsum ptr = case !(out ptr) of
  MkOut 0 el => pure 0
  MkOut 1 el => do
    (l # b # r) <- layer el
    pure (!(rsum l) + cast (getSingleton b) + !(rsum r))

rightmost : Maybe Bits8 -> Pointer.Mu Tree t -> IO (Maybe Bits8)
rightmost dflt t = case !(out t) of
  MkOut 0 el => pure dflt
  MkOut 1 el => do
    (_ # b # r) <- layer el
    rightmost (Just (getSingleton b)) r

namespace Data

  public export
  size : Data.Mu Tree -> Nat
  size = fold $ \ k, v => case k of
    0 => 0
    1 => let (l, _, r) = v in S (l + r)

  public export
  sum : Data.Mu Tree -> Nat
  sum = fold $ \ k, v => case k of
    0 => 0
    1 => let (l, b, r) = v in l + cast b + r

namespace Pointer

  export
  size : {0 t : Data.Mu Tree} -> Pointer.Mu Tree t ->
         IO (Singleton (Data.size t))
  size ptr = case !(out ptr) of
    MkOut 0 el => pure (MkSingleton 0)
    MkOut 1 el => do
      (l # _ # r) <- layer el
      m <- size l
      n <- size r
      pure (S <$> (plus <$> m <*> n))

  sum : {0 t : Data.Mu Tree} ->
        Pointer.Mu Tree t ->
        IO (Singleton (Data.sum t))
  sum ptr = case !(out ptr) of
    MkOut 0 el => pure (MkSingleton 0)
    MkOut 1 el => do
      (l # b # r) <- layer el
      m <- sum l
      n <- sum r
      pure (plus <$> (plus <$> m <*> cast <$> b) <*> n)

||| initFromFile creates a pointer to a datastructure stored in a file
||| @ cs   is the datatype you want to use to decode the buffer's content
||| @ safe signals whether to check the file's header matches the declared datatype
initFromFile : {default True safe : Bool} ->  (cs : Data) -> String -> IO (Exists (Pointer.Mu cs))
initFromFile cs fp
  = do Right buf <- createBufferFromFile fp
         | Left err => failWith (show err)
       skip <- getInt buf 0
       when safe $ do
         cs' <- getData buf 8
         unless (cs == cs') $ failWith $ unlines
           [ "Description mismatch:"
           , "expected:"
           , showData cs
           , "but got:"
           , showData cs'
           ]
       pure (Evidence t (MkMu buf (skip + 8)))

  where 0 t : Data.Mu cs -- postulated as an abstract value

main : IO ()
main = do
  writeToFile "tmp" example
  Evidence _ tree <- initFromFile Tree "tmp"
  putStrLn "RSum: \{show !(rsum tree)}"
  putStrLn "Sum: \{show !(sum tree)}"
  putStrLn "Rightmost: \{show !(rightmost Nothing tree)}"
  putStrLn "Tree size: \{show !(size tree)}"
