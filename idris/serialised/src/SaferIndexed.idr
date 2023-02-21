module SaferIndexed

import Data.Fin
import Data.DPair
import Data.Vect
import Data.Buffer
import System.File.Buffer

import Decidable.Equality

import Data.String
import Data.Singleton

import Lib
import Serialised.Desc

%default total

blockSize : Int
blockSize = 1000

namespace Data

  data All' : (d : Desc s n b) -> (p : x -> Type) -> Meaning d x -> Type

  public export
  All : (d : Desc s n b) -> (p : x -> Type) -> Meaning d x -> Type
  All None p t = ()
  All Byte p t = Singleton t
  All d@(Prod _ _) p t = All' d p t
  All Rec p t = p t

  public export
  data All' : (d : Desc s n b) -> (p : x -> Type) -> Meaning d x -> Type where
    (#) : All d p t -> All e p u -> All' (Prod d e) p (t # u)

  export
  all : (d : Desc s n b) -> ((a : x) -> p a) ->
        (t : Meaning d x) -> All d p t
  all None f t = t
  all Byte f t = MkSingleton t
  all (Prod d e) f (t # u) = (all d f t # all e f u)
  all Rec f t = f t

  public export
  AllK : (d : Desc s n b) -> (p : x -> Type) -> Meaning d x -> Type -> Type
  AllK None p t r = r
  AllK Byte p t r = Singleton t -> r
  AllK (Prod d e) p t r = AllK d p (fst t) (AllK e p (snd t) r)
  AllK Rec p t r = p t -> r

  export
  curry : {0 p : x -> Type} -> (d : Desc s n b) ->
          {0 t : Meaning d x} -> (All d p t -> r) -> AllK d p t r
  curry None f = f ()
  curry Byte f = f
  curry (Prod d e) f
    = SaferIndexed.Data.curry d {r = AllK e p (snd t) r}
    $ \ v => SaferIndexed.Data.curry e
    $ \ w => f (rewrite etaPair t in v # w)
  curry Rec f = f

namespace Serialising

  export
  record Serialising (cs : Data nm) (t : Data.Mu cs) where
    constructor MkSerialising
    runSerialising : Buffer -> Int -> IO Int

  export
  (>>=) : IO a -> (a -> Serialising cs t) -> Serialising cs t
  io >>= f = MkSerialising $ \buf, start =>
               do x <- io
                  runSerialising (f x) buf start

  parameters (buf : Buffer)

    goMeaning : Int ->
                {b : Bool} -> (d : Desc s n b) ->
                {0 t : Meaning d (Data.Mu cs)} ->
                All d (Serialising cs) t ->
                IO (Vect n Int, Int)
    goMeaning start None layer = pure ([], start)
    goMeaning start Byte layer = ([], start + 1) <$ setBits8 buf start (getSingleton layer)
    goMeaning start (Prod d e) (v # w)
      = do (n1, afterLeft) <- goMeaning start d v
           (n2, afterRight) <- goMeaning afterLeft e w
           pure (n1 ++ n2, afterRight)
    goMeaning start Rec layer
      = do end <- runSerialising layer buf start
           pure $ (,end) $ if b then [] else [end - start]

    goMu : Int ->
           (k : Fin (consNumber cs)) -> (c : Constructor _) ->
           {0 t : Meaning (description c) (Data.Mu cs)} ->
           All (description c) (Serialising cs) t ->
           IO Int
    goMu start k cons layer
      = do -- [ Tag | ... offsets ... | ... meaning ... ]
           setBits8 buf start (cast $ cast {to = Nat} k)
           let afterTag  = start + 1
           let afterOffs = afterTag + 8 * cast (offsets cons)
           (is, end) <- goMeaning afterOffs (description cons) layer
           setInts buf afterTag is
           pure end

  export
  setMu : {cs : Data nm} -> (k : Index cs) ->
          {0 t : Meaning (description k) (Data.Mu cs)} ->
          All (description k) (Serialising cs) t ->
          Serialising cs (k # t)
  setMu (MkIndex k) layer
    = MkSerialising $ \ buf, start =>
        goMu buf start k (index k $ constructors cs) layer

  export
  setMuK : (cs : Data nm) -> (k : Index cs) ->
           {0 t : Meaning (description k) (Data.Mu cs)} ->
           AllK (description k) (Serialising cs) t (Serialising cs (k # t))
  setMuK cs (MkIndex k) with (index k $ constructors cs)
    _ | cons = SaferIndexed.Data.curry (description cons) $ \ layer =>
               MkSerialising $ \ buf, start => goMu buf start k cons layer

  export
  serialiseToFile : {cs : Data nm} -> String -> {0 t : Mu cs} ->
                    Serialising cs t -> IO ()
  serialiseToFile fp t = do
    Just buf <- newBuffer blockSize
      | Nothing => failWith "\{__LOC__} Couldn't allocate buffer"
    end <- setData buf 8 cs
    setInt buf 0 (end - 8)
    size <- runSerialising t buf end
    Right () <- writeBufferToFile fp buf size
      | Left (err, _) => failWith (show err)
    pure ()

namespace Buffer

  setMu : {cs : Data nm} -> (t : Data.Mu cs) -> Serialising cs t
  setMu (k # t)
    = Serialising.setMu k
    $ all (description k) (assert_total Buffer.setMu) t

  export
  writeToFile : {cs : Data nm} -> String -> Mu cs -> IO ()
  writeToFile fp t = serialiseToFile fp (setMu t)

namespace Pointer

  record Elem (d : Desc s n b) (cs : Data nm) (t : Meaning d (Data.Mu cs)) where
    constructor MkElem
    subterms : Vect n Int
    elemBuffer : Buffer
    elemPosition : Int

  record Mu (cs : Data nm) (t : Data.Mu cs) where
    constructor MkMu
    muBuffer : Buffer
    muPosition : Int

  namespace Poke

    public export
    data Poke' : (d : Desc s n b) -> (cs : Data nm) -> Meaning d (Data.Mu cs) -> Type

    public export
    Poke : (d : Desc s n b) -> (cs : Data nm) -> Meaning d (Data.Mu cs) -> Type
    Poke None _ t = ()
    Poke Byte cs t = Singleton t
    Poke d@(Prod _ _) cs t = Poke' d cs t
    Poke Rec cs t = Pointer.Mu cs t

    data Poke' : (d : Desc s n b) -> (cs : Data nm) -> Meaning d (Data.Mu cs) -> Type where
      (#) : Elem d cs t -> Elem e cs u -> Poke' (Prod d e) cs (t # u)

    export
    poke : {0 cs : Data nm} -> {s : Nat} -> {d : Desc s n b} ->
           forall t. Elem d cs t -> IO (Poke d cs t)
    poke {d = None} el = pure ()
    poke {d = Byte} el = do
      bs <- getBits8 (elemBuffer el) (elemPosition el)
      pure (believe_me $ MkSingleton bs)
    poke {d = Prod {sl} d e} {t} el = do
      let (n1, n2) = splitAt _ (subterms el)
      let left = MkElem n1 (elemBuffer el) (elemPosition el)
      let pos = elemPosition el + sum n1 + cast sl
      let right = MkElem n2 (elemBuffer el) pos
      pure (rewrite etaPair t in left # right)
    poke {d = Rec} el = pure (MkMu (elemBuffer el) (elemPosition el))

  namespace Layer

    public export
    data Layer' : (d : Desc s n b) -> (cs : Data nm) -> Meaning d (Data.Mu cs) -> Type

    public export
    Layer : (d : Desc s n b) -> (cs : Data nm) -> Meaning d (Data.Mu cs) -> Type
    Layer d@(Prod _ _) cs t = Layer' d cs t
    Layer None _ _ = ()
    Layer Byte _ t = Singleton t
    Layer Rec cs t = Pointer.Mu cs t

    data Layer' : (d : Desc s n b) -> (cs : Data nm) -> Meaning d (Data.Mu cs) -> Type where
      (#) : Layer d cs t -> Layer e cs u -> Layer' (Prod d e) cs (t # u)

    export
    layer : {0 cs : Data nm} -> {s : Nat} -> {d : Desc s n b} ->
            forall t. Elem d cs t -> IO (Layer d cs t)
    layer el = poke el >>= go d where

      go : forall n, b. {s : Nat} -> (d : Desc s n b) ->
           forall t. Poke d cs t -> IO (Layer d cs t)
      go None p = pure ()
      go Byte p = pure p
      go (Prod d e) (p # q) = [| layer p # layer q |]
      go Rec p = pure p

  data Out : (cs : Data nm) -> (t : Data.Mu cs) -> Type where
    (#) : (k : Index cs) ->
          forall t. Elem (description k) cs t ->
          Out cs (k # t)

  out : {cs : Data nm} -> forall t. Pointer.Mu cs t -> IO (Out cs t)
  out {t} mu = do
    tag <- getBits8 (muBuffer mu) (muPosition mu)
    let Just k = natToFin (cast tag) (consNumber cs)
      | _ => failWith "Invalid representation"
    let k = MkIndex k
    let 0 sub = unfoldAs k t
    val <- (k #) <$> getConstructor k {t = sub.fst} (rewrite sym sub.snd in mu)
    pure (rewrite sub.snd in val)

    where

    -- postulated, utterly unsafe
    0 unfoldAs :
      (k : Index cs) -> (t : Data.Mu cs) ->
      (val : Meaning (description k) (Data.Mu cs)
       ** t === (k # val))
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
      (k : Index cs) ->
      forall t.
      Pointer.Mu cs (k # t) ->
      IO (Elem (description k) cs t)
    getConstructor (MkIndex k) mu
      = getOffsets (muBuffer mu) (1 + muPosition mu) (offsets (index k $ constructors cs))
      $ \ subterms, pos => MkElem subterms (muBuffer mu) pos

  namespace View

    public export
    data View : (cs : Data nm) -> (t : Data.Mu cs) -> Type where
      (#) : (k : Index cs) ->
            forall t. Layer (description k) cs t ->
            View cs (k # t)

    export
    view : {cs : Data nm} -> forall t. Pointer.Mu cs t -> IO (View cs t)
    view ptr = do k # el <- out ptr
                  vs <- layer el
                  pure (k # vs)

namespace Tree

  ||| Tree sum
  sum : Data.Mu Tree -> Nat
  sum t = case t of
    "Leaf" # _ => 0
    "Node" # l # b # r =>
      let m = sum l
          n = sum r
      in (m + cast b + n)

namespace Raw

  ||| Raw sum
  export
  sum : Pointer.Mu Tree _ -> IO Nat
  sum ptr = case !(view ptr) of
    "Leaf" # _ => pure 0
    "Node" # l # b # r =>
      do m <- sum l
         n <- sum r
         pure (m + cast b + n)

rightmost : Maybe Bits8 -> Pointer.Mu Tree t -> IO (Maybe Bits8)
rightmost dflt t = case !(out t) of
  "Leaf" # el => pure dflt
  "Node" # el => do
    (_ # b # r) <- layer el
    rightmost (Just (getSingleton b)) r

-- Here we define the functional specification of the functions we
-- want to write over pointers. This will, via Singleton & Serialising,
-- allow us to write correct by construction effectful functions
namespace Data

  ||| The size of the tree is given by the number of nodes
  public export
  size : Data.Mu Tree -> Nat
  size = fold $ \ k, v => case k of
    "Leaf" => 0
    "Node" => let (l # _ # r) = v in S (l + r)

  ||| The sum of the tree's node is given by casting the Bits8 nodes
  ||| to Nat and summing them up
  public export
  sum : Data.Mu Tree -> Nat
  sum = fold $ \ k, v => case k of
    "Leaf" => 0
    "Node" => let (l # b # r) = v in l + cast b + r

  ||| Map is obtained by applying a function transforming Bit8 values
  ||| to all of the Bits8 stored in the tree's nodes
  public export
  map : (Bits8 -> Bits8) -> Data.Mu Tree -> Data.Mu Tree
  map f = fold $ \ k, v => case k of
    "Leaf" => leaf
    "Node" => let (l # b # r) = v in node l (f b) r

-- Here we define the effectful functions processing a pointer
-- IO allows us to inspect the content addressed by the pointer to take the tree apart
-- Serialising lets us build a specified output tree
namespace Pointer

  ||| Correct by construction size function.
  ||| @ t   is the phantom name of the tree represented by the buffer
  ||| @ ptr is the position of t inside the buffer
  ||| Singleton ensures that the value we return is the same as if
  ||| we had directly processed `t`.
  export
  size : (ptr : Pointer.Mu Tree t) ->
         IO (Singleton (Data.size t))
  size ptr = case !(out ptr) of
    "Leaf" # t => pure [| Z |]
    "Node" # t => do
      l # br <- poke t
      m <- size !(poke l)
      _ # r <- poke br
      n <- size !(poke r)
      pure [| S [| m + n |] |]

  ||| Correct by construction sum function.
  ||| @ t   is the phantom name of the tree represented by the buffer
  ||| @ ptr is the position of t inside the buffer
  ||| Singleton ensures that the value we return is the same as if
  ||| we had directly processed `t`.
  export
  sum : (ptr : Pointer.Mu Tree t) ->
        IO (Singleton (Data.sum t))
  sum ptr = case !(view ptr) of
    "Leaf" # t => pure (MkSingleton 0)
    "Node" # l # b # r =>
      do m <- sum l
         n <- sum r
         pure [| [| m + [| cast b |] |] + n |]

  export
  leaf : Serialising Tree Tree.leaf
  leaf = setMuK Tree 0

  export
  node : Serialising Tree l -> Singleton b -> Serialising Tree r ->
            Serialising Tree (Tree.node l b r)
  node = setMuK Tree 1

  ||| Correct by construction map function.
  ||| @ f   is the function to map over the tree's nodes
  ||| @ t   is the phantom name of the tree represented by the buffer
  ||| @ ptr is the position of t inside the buffer
  ||| Serialising ensures that the value we compute is the same as if
  ||| we had directly processed `t`.
  export
  map : (f : Bits8 -> Bits8) ->
        (ptr : Pointer.Mu Tree t) ->
        Serialising Tree (Data.map f t)
  map f ptr = case !(view ptr) of
    "Leaf" # () => leaf
    "Node" # l # b # r => node (map f l) (f <$> b) (map f r)

  ||| Simple printing function
  export
  display : Pointer.Mu Tree t -> IO String
  display ptr = case !(out ptr) of
    "Leaf" # t => pure "Leaf"
    "Node" # t => do
      (l # b # r) <- layer t
      l <- display l
      r <- display r
      pure "(node \{l} \{show (getSingleton b)} \{r})"

namespace Serialising

  export
  execSerialising : {cs : Data nm} -> {0 t : Data.Mu cs} ->
                    Serialising cs t -> IO (Pointer.Mu cs t)
  execSerialising act = do
    Just buf <- newBuffer blockSize
      | Nothing => failWith "\{__LOC__} Couldn't allocate buffer"
    -- Do we care about storing the data description in this case?
    end <- setData buf 8 cs
    setInt buf 0 (end - 8)
    -- Anyway, here's the actual data:
    size <- runSerialising act buf end
    pure (MkMu buf end)


||| initFromFile creates a pointer to a datastructure stored in a file
||| @ cs   is the datatype you want to use to decode the buffer's content
||| @ safe signals whether to check the file's header matches the declared datatype
initFromFile : {default True safe : Bool} ->  (cs : Data nm) -> String -> IO (Exists (Pointer.Mu cs))
initFromFile cs fp
  = do Right buf <- createBufferFromFile fp
         | Left err => failWith (show err)
       skip <- getInt buf 0
       when safe $ do
         cs' <- getData buf 8
         unless (eqData cs cs') $ failWith $ unlines
           [ "Description mismatch:"
           , "expected:"
           , show cs
           , "but got:"
           , show cs'
           ]
       pure (Evidence t (MkMu buf (skip + 8)))

  where 0 t : Data.Mu cs -- postulated as an abstract value


testing : Pointer.Mu Tree t -> IO ()
testing tree = do
  putStrLn "Tree: \{!(display tree)}"
  putStrLn "RSum: \{show !(Raw.sum tree)}"
  putStrLn "Sum: \{show !(Pointer.sum tree)}"
  putStrLn "Rightmost: \{show !(rightmost Nothing tree)}"
  putStrLn "Tree size: \{show !(size tree)}"

main : IO ()
main = do
  -- First Tree
  writeToFile "tmp" example
  Evidence _ tree <- initFromFile Tree "tmp"
  testing tree

  putStrLn (replicate 72 '-')

  -- Second Tree: mapping over the first one
  serialiseToFile "tmp2" (map (1+) tree)
  Evidence _ tree2 <- initFromFile Tree "tmp2"
  testing tree2

  putStrLn (replicate 72 '-')

  -- Third Tree: don't go via a file
  tree3 <- execSerialising (map (2+) tree2)
  testing tree3
