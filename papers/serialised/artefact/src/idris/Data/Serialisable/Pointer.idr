module Data.Serialisable.Pointer

import Data.Fin
import Data.DPair
import Data.Vect
import Data.Buffer
import System.File.Buffer

import Decidable.Equality

import Data.String
import Data.Singleton

import Lib
import Data.Serialisable.Desc
import Data.Serialisable.Data

%default total

-- TODO: use a builder instead of allocating a massive block
blockSize : Int
blockSize = 66666000

namespace Pointer

  ||| Pointer to a meaning, parametrised by a phantom
  ||| copy of the value it points to
  export
  record Meaning (d : Desc r s o) (cs : Data nm) (t : Data.Meaning d (Data.Mu cs)) where
    constructor MkMeaning
    subterms : Vect o Int
    meaningBuffer : Buffer
    meaningPosition : Int
    meaningSize : Int


  ||| Pointer to a tree, parametrised by a phantom
  ||| copy of the value it points to
  export
  record Mu (cs : Data nm) (t : Data.Mu cs) where
    constructor MkMu
    muBuffer : Buffer
    muPosition : Int
    muSize : Int

------------------------------------------------------------------------
-- Loading a pointer to a value from a file

||| initFromFile creates a pointer to a datastructure stored in a file
||| @ cs   is the datatype you want to use to decode the buffer's content
||| @ safe signals whether to check the file's header matches the declared datatype
export
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

------------------------------------------------------------------------
-- Poking the buffer to observe a meaning's head constructor

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

------------------------------------------------------------------------
-- Extracting a whole layer

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

------------------------------------------------------------------------
-- Observing a tree's head constructor

namespace Out

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

    getConstructor :
      (k : Index cs) ->
      forall t.
      Pointer.Mu cs (k # t) ->
      IO (Pointer.Meaning (description k) cs t)
    getConstructor (MkIndex k) mu
      = let offs : Nat; offs = offsets (index k $ constructors cs) in
        getOffsets (muBuffer mu) (1 + muPosition mu) offs
      $ let size = muSize mu - 1 - cast (8 * offs) in
        \ subterms, pos => MkMeaning subterms (muBuffer mu) pos size

------------------------------------------------------------------------
-- Combining `out` and `layer` to define a view exposing a tree's top
-- constructor and its arguments

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

------------------------------------------------------------------------
-- Implementing counterparts to `fmap`, `traverse`, and `fold`
-- working directly on serialised data

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

------------------------------------------------------------------------
-- Deserialising by repeatedly using `view`

export
deserialise : {cs : Data nm} -> forall t. Mu cs t -> IO (Singleton t)
deserialise ptr = do
  k # ptr <- out ptr
  t <- assert_total (fmap (description k) id deserialise ptr)
  pure ((k #) <$> transport (fmapId (description k) id (\ _ => Refl) _) t)

------------------------------------------------------------------------
-- Serialising values

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
  serialise : {cs : Data nm} -> (t : Data.Mu cs) -> Serialising cs t
  serialise (k # t) = k # all (description k) (assert_total serialise) t

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

------------------------------------------------------------------------
-- Various implementations of copy : Pointer.Mu cs t -> Serialising cs t

export
||| This is the efficient one, using the `copyData` primitive
copy : Pointer.Mu cs t -> Serialising cs t
copy ptr = MkSerialising $ \ buf, pos =>
  let size = muSize ptr in
  pos + size <$ copyData {io = IO} (muBuffer ptr) (muPosition ptr) size buf pos

export
||| Implementation interleaving calls to poke and corresponding writes
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
||| Naïve implementation by composing deserialisation and serialisation
roundtripCopy : {cs : Data nm} -> forall t. Pointer.Mu cs t -> Serialising cs t
roundtripCopy ptr = do
  MkSingleton t <- deserialise ptr
  serialise t
