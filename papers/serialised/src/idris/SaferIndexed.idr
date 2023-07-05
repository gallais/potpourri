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
blockSize = 66666000

namespace Data

  data All' : (d : Desc r s o) -> (p : x -> Type) -> Meaning d x -> Type

  public export
  All : (d : Desc r s o) -> (p : x -> Type) -> Meaning d x -> Type
  All None p t = ()
  All Byte p t = Singleton t
  All d@(Prod _ _) p t = All' d p t
  All Rec p t = p t

  public export
  data All' : (d : Desc r s o) -> (p : x -> Type) -> Meaning d x -> Type where
    (#) : All d p t -> All e p u -> All' (Prod d e) p (t # u)

  export
  all : (d : Desc r s o) -> ((a : x) -> p a) ->
        (t : Meaning d x) -> All d p t
  all None f t = t
  all Byte f t = MkSingleton t
  all (Prod d e) f (t # u) = (all d f t # all e f u)
  all Rec f t = f t

  public export
  AllK : (d : Desc r s o) -> (p : x -> Type) -> Meaning d x -> Type -> Type
  AllK None p t r = r
  AllK Byte p t r = Singleton t -> r
  AllK (Prod d e) p t r = AllK d p (fst t) (AllK e p (snd t) r)
  AllK Rec p t r = p t -> r

  export
  curry : {0 p : x -> Type} -> (d : Desc r s o) ->
          {0 t : Meaning d x} -> (All d p t -> a) -> AllK d p t a
  curry None f = f ()
  curry Byte f = f
  curry (Prod d e) f
    = SaferIndexed.Data.curry d {a = AllK e p (snd t) a}
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
                {r : Bool} -> (d : Desc r s o) ->
                {0 t : Meaning d (Data.Mu cs)} ->
                All d (Serialising cs) t ->
                IO (Vect o Int, Int)
    goMeaning start None layer = pure ([], start)
    goMeaning start Byte layer = ([], start + 1) <$ setBits8 buf start (getSingleton layer)
    goMeaning start (Prod d e) (v # w)
      = do (n1, afterLeft) <- goMeaning start d v
           (n2, afterRight) <- goMeaning afterLeft e w
           pure (n1 ++ n2, afterRight)
    goMeaning start Rec layer
      = do end <- runSerialising layer buf start
           pure $ (,end) $ if r then [] else [end - start]

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
  (#) : {cs : Data nm} -> (k : Index cs) ->
        {0 t : Meaning (description k) (Data.Mu cs)} ->
        All (description k) (Serialising cs) t ->
        Serialising cs (k # t)
  MkIndex k # layer
    = MkSerialising $ \ buf, start =>
        goMu buf start k (index k $ constructors cs) layer

  export
  setMuK : (cs : Data nm) -> (k : Index cs) ->
           {0 t : Meaning (description k) (Data.Mu cs)} ->
           AllK (description k) (Serialising cs) t (Serialising cs (k # t))
  setMuK cs (MkIndex k) with (index k $ constructors cs)
    _ | cons = SaferIndexed.Data.curry (description cons) $ \ layer =>
               MkSerialising $ \ buf, start => goMu buf start k cons layer

namespace Buffer

  export
  serialise : {cs : Data nm} -> (t : Data.Mu cs) -> Serialising cs t
  serialise (k # t) = k # all (description k) (assert_total serialise) t

namespace Pointer

  export
  record Meaning (d : Desc r s o) (cs : Data nm) (t : Data.Meaning d (Data.Mu cs)) where
    constructor MkMeaning
    subterms : Vect o Int
    meaningBuffer : Buffer
    meaningPosition : Int
    meaningSize : Int

  export
  record Mu (cs : Data nm) (t : Data.Mu cs) where
    constructor MkMu
    muBuffer : Buffer
    muPosition : Int
    muSize : Int

  namespace Poke

    public export
    data Poke' : (d : Desc r s o) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type

    public export
    Poke : (d : Desc r s o) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type
    Poke None _ t = ()
    Poke Byte cs t = Singleton t
    Poke d@(Prod _ _) cs t = Poke' d cs t
    Poke Rec cs t = Pointer.Mu cs t

    data Poke' : (d : Desc r s o) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type where
      (#) : Pointer.Meaning d cs t -> Pointer.Meaning e cs u -> Poke' (Prod d e) cs (t # u)

    %spec d
    %inline
    export
    poke : {0 cs : Data nm} -> {d : Desc r s o} ->
           forall t. Pointer.Meaning d cs t -> IO (Poke d cs t)
    poke {d = None} el = pure ()
    poke {d = Byte} el = do
      bs <- getBits8 (meaningBuffer el) (meaningPosition el)
      pure (unsafeMkSingleton bs)
    poke {d = Prod {sl} d e} {t} el = do
      let (n1, n2) = splitAt _ (subterms el)
      let lsize = sum n1 + cast sl
      let left = MkMeaning n1 (meaningBuffer el) (meaningPosition el) lsize
      let pos = meaningPosition el + lsize
      let right = MkMeaning n2 (meaningBuffer el) pos (meaningSize el - lsize)
      pure (rewrite etaPair t in left # right)
    poke {d = Rec} el = pure (MkMu (meaningBuffer el) (meaningPosition el) (meaningSize el))

  namespace Layer

    public export
    data Layer' : (d : Desc r s o) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type

    public export
    Layer : (d : Desc r s o) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type
    Layer d@(Prod _ _) cs t = Layer' d cs t
    Layer None _ _ = ()
    Layer Byte _ t = Singleton t
    Layer Rec cs t = Pointer.Mu cs t

    data Layer' : (d : Desc r s o) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type where
      (#) : Layer d cs t -> Layer e cs u -> Layer' (Prod d e) cs (t # u)


    %spec d
    %inline
    export
    layer : {0 cs : Data nm} -> {d : Desc r s o} ->
            forall t. Pointer.Meaning d cs t -> IO (Layer d cs t)
    layer el = poke el >>= go d where

      go : forall r, s, o. (d : Desc r s o) ->
           forall t. Poke d cs t -> IO (Layer d cs t)
      go None p = pure ()
      go Byte p = pure p
      go (Prod d e) (p # q) = [| layer p # layer q |]
      go Rec p = pure p

  public export
  getIndex : {cs : Data nm} -> forall t. Pointer.Mu cs t -> IO (Index cs)
  getIndex mu = do
    tag <- getBits8 (muBuffer mu) (muPosition mu)
    let Just k = natToFin (cast tag) (consNumber cs)
      | _ => failWith "Invalid representation"
    pure (MkIndex k)

  public export
  data Out : (cs : Data nm) -> (t : Data.Mu cs) -> Type where
    (#) : (k : Index cs) ->
          forall t. Pointer.Meaning (description k) cs t ->
          Out cs (k # t)

  %spec cs
  %inline
  export
  out : {cs : Data nm} -> forall t. Pointer.Mu cs t -> IO (Out cs t)
  out {t} mu = do
    k <- getIndex mu
    let 0 sub = unfoldAs k t
    val <- (k #) <$> getConstructor k {t = sub.fst} (rewrite sym sub.snd in mu)
    pure (rewrite sub.snd in val)

    where

    -- postulated, utterly unsafe
    %unsafe
    0 unfoldAs :
      (k : Index cs) -> (t : Data.Mu cs) ->
      (val : Data.Meaning (description k) (Data.Mu cs)
       ** t === (k # val))
{-
    unfoldAs k (l@_ # val) with (decEq k l)
      _ | Yes Refl = (val ** Refl)
      _ | No _ = failWith "The IMPOSSIBLE has happened"
-}

    getOffsets : Buffer -> Int -> -- Buffer & position
                 (n : Nat) ->
                 forall t. (Vect n Int -> Int -> Pointer.Meaning d cs t) ->
                 IO (Pointer.Meaning d cs t)
    getOffsets buf pos 0 k = pure (k [] pos)
    getOffsets buf pos (S n) k = do
      off <- getInt buf pos
      getOffsets buf (8 + pos) n (k . (off ::))

    %inline
    getConstructor :
      (k : Index cs) ->
      forall t.
      Pointer.Mu cs (k # t) ->
      IO (Pointer.Meaning (description k) cs t)
    getConstructor (MkIndex k) mu
      = let %inline offs : Nat; offs = offsets (index k $ constructors cs) in
        getOffsets (muBuffer mu) (1 + muPosition mu) offs
      $ let size = muSize mu - 1 - cast (8 * offs) in
        \ subterms, pos => MkMeaning subterms (muBuffer mu) pos size

  namespace View

    public export
    data View : (cs : Data nm) -> (t : Data.Mu cs) -> Type where
      (#) : (k : Index cs) ->
            forall t. Layer (description k) cs t ->
            View cs (k # t)


    %spec cs
    %inline
    export
    view : {cs : Data nm} -> forall t. Pointer.Mu cs t -> IO (View cs t)
    view ptr = do k # el <- out ptr
                  vs <- layer el
                  pure (k # vs)

    export
    fmap : (d : Desc{}) ->
           (0 f : Mu cs -> b) ->
           (forall t. Mu cs t -> IO (Singleton (f t))) ->
           forall t. Meaning d cs t ->
           IO (Singleton (Data.fmap d f t))
    fmap d f act ptr = poke ptr >>= go d where

      go : (d : Desc{}) -> forall t. Poke d cs t -> IO (Singleton (Data.fmap d f t))
      go None {t} v = pure byIrrelevance
      go Byte v = pure v
      go (Prod d e) (v # w)
        = do v <- fmap d f act v
             w <- fmap e f act w
             pure [| v # w |]
      go Rec v = act v

    export
    traverse : Monad m => (d : Desc{}) ->
               (0 f : Mu cs -> m b) ->
               (forall t. Mu cs t -> IO (Singleton (f t))) ->
               forall t. Meaning d cs t ->
               IO (Singleton (Data.traverse d f t))
    traverse d f act v = poke v >>= go d where

      go : (d : Desc{}) -> forall t. Poke d cs t -> IO (Singleton (Data.traverse d f t))
      go None {t} v = pure (pure <$> byIrrelevance)
      go Byte v = pure [| pure v |]
      go (Prod d e) (v # w)
        = do v <- traverse d f act v
             w <- traverse e f act w
             let v = [| pure (pure (#)) <*> v |]
             pure [| v <*> w |]
      go Rec v = act v

    export
    fold : {cs : Data nm} -> (alg : Alg cs a) ->
           forall t. Mu cs t -> IO (Singleton (Data.fold alg t))
    fold alg ptr
      = do k # t <- out ptr
           rec <- assert_total (fmap (description k) _ (fold alg) t)
           pure (alg k <$> rec)

    export
    deserialise : {cs : Data nm} -> forall t. Mu cs t -> IO (Singleton t)
    deserialise ptr = do
      k # ptr <- out ptr
      t <- assert_total (fmap (description k) id deserialise ptr)
      pure ((k #) <$> transport (fmapId (description k) id (\ _ => Refl) _) t)

namespace SerialisingInContext

  public export
  AllInContext : (d : Desc r s o) -> (p, q : x -> Type) -> Meaning d x -> Type

  public export
  data AllInContext' : (d : Desc r s o) -> (p, q : x -> Type) -> Meaning d x -> Type

  AllInContext None p q t = ()
  AllInContext Byte p q t = Singleton t
  AllInContext d@(Prod _ _) p q t = AllInContext' d p q t
  AllInContext Rec p q t = p t

  data AllInContext' : (d : Desc r s o) -> (p, q : x -> Type) -> Meaning d x -> Type where
    (#) : AllInContext d p q s ->
          (All d q s -> AllInContext e p q t) ->
          AllInContext' (Prod d e) p q (s # t)


  parameters (buf : Buffer)

    goMeaning : Int ->
                {r : Bool} -> (d : Desc r s o) ->
                {0 t : Meaning d (Data.Mu cs)} ->
                AllInContext d (Serialising cs) (Pointer.Mu cs) t ->
                IO (Vect o Int, Int, All d (Pointer.Mu cs) t)
    goMeaning start None layer = pure ([], start, ())
    goMeaning start Byte layer = ([], start + 1, layer) <$ setBits8 buf start (getSingleton layer)
    goMeaning start (Prod d e) (v # w)
      = do (n1, afterLeft, ps) <- goMeaning start d v
           (n2, afterRight, qs) <- goMeaning afterLeft e (w ps)
           pure (n1 ++ n2, afterRight, ps # qs)
    goMeaning start Rec layer
      = do end <- runSerialising layer buf start
           let size = end - start
           pure $ (if r then [] else [size], end, MkMu buf start size)

    goMu : Int ->
           (k : Fin (consNumber cs)) -> (c : Constructor _) ->
           {0 t : Meaning (description c) (Data.Mu cs)} ->
           AllInContext (description c) (Serialising cs) (Pointer.Mu cs) t ->
           IO Int
    goMu start k cons layer
      = do -- [ Tag | ... offsets ... | ... meaning ... ]
           setBits8 buf start (cast $ cast {to = Nat} k)
           let afterTag  = start + 1
           let afterOffs = afterTag + 8 * cast (offsets cons)
           (is, end, ps) <- goMeaning afterOffs (description cons) layer
           setInts buf afterTag is
           pure end

  infixr 5 ##
  export
  (##) : {cs : Data nm} -> (k : Index cs) ->
         {0 t : Meaning (description k) (Data.Mu cs)} ->
         AllInContext (description k) (Serialising cs) (Pointer.Mu cs) t ->
         Serialising cs (k # t)
  MkIndex k ## layer
    = MkSerialising $ \ buf, start =>
        SerialisingInContext.goMu buf start k (index k $ constructors cs) layer

namespace Serialising

  export
  copy : Pointer.Mu cs t -> Serialising cs t
  copy ptr = MkSerialising $ \ buf, pos =>
    let size = muSize ptr in
    pos + size <$ copyData {io = IO} (muBuffer ptr) (muPosition ptr) size buf pos

  export
  deepCopy : {cs : Data nm} -> forall t. Pointer.Mu cs t -> Serialising cs t
  deepCopy ptr = do
    k # ptr <- out ptr
    k # !(go ? ptr)

   where

     go : (d : Desc r s o) -> forall t.
          Pointer.Meaning d cs t -> IO (All d (Serialising cs) t)
     go None ptr = pure ()
     go Byte ptr = poke ptr
     go (Prod d e) ptr = do
       ptrl # ptrr <- poke ptr
       [| go d ptrl # go e ptrr |]
     go Rec ptr = pure (deepCopy !(poke ptr))

  export
  roundtripCopy : {cs : Data nm} -> forall t. Pointer.Mu cs t -> Serialising cs t
  roundtripCopy ptr = do
    MkSingleton t <- deserialise ptr
    serialise t

namespace Tree

  ||| Tree sum
  export
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

namespace Data

  public export
  rightmost : ATree -> Maybe Bits8
  rightmost t = case t of
    "Leaf" # _ => Nothing
    "Node" # l # b # r => Just (fromMaybe b (rightmost r))

namespace Pointer

  export
  rightmost : Pointer.Mu Tree t -> IO (Singleton (rightmost t))
  rightmost t = case !(view t) of
    "Leaf" # el => pure [| Nothing |]
    "Node" # _ # b # r => map ((Just <$>) . (fromMaybe . delay <$> b <*>)) (rightmost r)

-- Here we define the functional specification of the functions we
-- want to write over pointers. This will, via Singleton & Serialising,
-- allow us to write correct by construction effectful functions
namespace Data

  ||| Tree with nodes carrying their level
  public export
  levels : (n : Nat) -> Data.Mu Tree
  levels 0 = leaf
  levels (S n) = node (levels n) (cast n) (levels n)

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

  export
  levels : (n : Nat) -> Serialising Tree (levels n)
  levels 0 = leaf
  levels (S n) = "Node" ## levels n # \ ih => pure (cast n) # \ _ => copy ih

  export
  deepLevels : (n : Nat) -> Serialising Tree (levels n)
  deepLevels 0 = leaf
  deepLevels (S n) = node (deepLevels n) (pure (cast n)) (deepLevels n)


  ||| Simple printing function
  export
  display : Pointer.Mu Tree t -> IO String
  display ptr = case !(out ptr) of
    "Leaf" # t => pure "leaf"
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
    middle <- setData buf 8 cs
    setInt buf 0 (middle - 8)
    end <- runSerialising act buf middle
    pure (MkMu buf middle (end - middle))


namespace Pointer

  export
  writeToFile : {cs : Data nm} -> String ->
                forall t. Pointer.Mu cs t -> IO ()
  writeToFile fp (MkMu buf pos size) = do
    desc <- getInt buf 0
    let start = 8 + desc
    let bufSize = 8 + desc + size
    buf <- if pos == start then pure buf else do
      Just newbuf <- newBuffer bufSize
        | Nothing => failWith "\{__LOC__} Couldn't allocate buffer"
      copyData buf 0 start newbuf 0
      copyData buf pos size newbuf start
      pure buf
    Right () <- writeBufferToFile fp buf bufSize
      | Left (err, _) => failWith (show err)
    pure ()

namespace Serialising

  export
  writeToFile : {cs : Data nm} -> String -> forall t. Serialising cs t -> IO ()
  writeToFile fp val = writeToFile fp !(execSerialising val)

namespace Data

  export
  writeToFile : {cs : Data nm} -> String -> Mu cs -> IO ()
  writeToFile fp t = writeToFile fp (serialise t)

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
       let pos = skip + 8
       pure (Evidence t (MkMu buf pos (!(rawSize buf) - pos)))

  where 0 t : Data.Mu cs -- postulated as an abstract value

namespace Data

  public export
  swap : Data.Mu Tree -> Data.Mu Tree
  swap ("Leaf" # _) = "Leaf" # ()
  swap ("Node" # l # b # r) = "Node" # r # b # l

  public export
  right : Data.Mu Tree -> Data.Mu Tree
  right ("Node" # _ # _ # r) = r
  right t = t

namespace Pointer

  export
  swap : Pointer.Mu Tree t -> Serialising Tree (Data.swap t)
  swap ptr = case !(view ptr) of
    "Leaf" # () => leaf
    "Node" # l # b # r => node (copy r) b (copy l)

  export
  deepSwap : Pointer.Mu Tree t -> Serialising Tree (Data.swap t)
  deepSwap ptr = case !(view ptr) of
    "Leaf" # () => leaf
    "Node" # l # b # r => node (deepCopy r) b (deepCopy l)

  export
  right : Pointer.Mu Tree t -> IO (Pointer.Mu Tree (Data.right t))
  right ptr = case !(view ptr) of
    "Leaf" # _ => pure ptr
    "Node" # l # b # r => pure r


testing : String -> Pointer.Mu Tree t -> IO ()
testing msg tree = do
  putStrLn (replicate 72 '-')
  putStrLn "Testing \{msg}"
  putStrLn "Tree: \{!(display tree)}"
  putStrLn "Swapped: \{!(display !(execSerialising (Pointer.swap tree)))}"
  putStrLn "DSum: \{show (Tree.sum (getSingleton !(deserialise tree)))}"
  putStrLn "RSum: \{show !(Raw.sum tree)}"
  putStrLn "Sum: \{show !(Pointer.sum tree)}"
  putStrLn "Rightmost: \{show !(rightmost tree)}"
  putStrLn "Tree size: \{show !(size tree)}"

testingFile : String -> IO (Exists (Pointer.Mu Tree))
testingFile fp = do
  Evidence _ tree <- initFromFile Tree fp
  testing fp tree
  pure (Evidence _ tree)

main : IO ()
main = do
  -- Empty Tree
  testing "execSerialising" !(execSerialising leaf)

  -- First Tree
  writeToFile "tmp" example
  Evidence _ tree1 <- testingFile "tmp"
  Evidence _ tree1Left <- testingFile "tmp-left"

  -- Second Tree: mapping over the first one
  writeToFile "tmp2" (map (1+) tree1)
  Evidence _ tree2 <- testingFile "tmp2"
  Evidence _ tree2Left <- testingFile "tmp2-left"

  -- Third Tree: don't go via a file
  tree3 <- execSerialising (map (2+) tree2)
  testing "map (2+) tree2" tree3

  -- Fourth Tree: focus on a subtree
  tree4 <- right tree3
  testing "right tree3" tree4

  -- Round-trip subtree via a file
  writeToFile "tmp3" (map (\ b => b - 20) tree4)
  Evidence _ tree5 <- testingFile "tmp3-left"

  pure ()
