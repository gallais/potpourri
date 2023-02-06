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

import Lib
import Serialised.Desc

%default total

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
    (#) : All d p t -> All e p u -> All' (Prod d e) p (t, u)

  export
  all : (d : Desc s n b) -> ((a : x) -> p a) ->
        (t : Meaning d x) -> All d p t
  all None f t = t
  all Byte f t = MkSingleton t
  all (Prod d e) f (t, u) = (all d f t # all e f u)
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
  record Serialising (cs : Data) (t : Data.Mu cs) where
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
           (k : Fin (length cs)) -> (c : Constructor) ->
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
  setMu : {cs : Data} -> (k : Fin (length cs)) ->
          {0 t : Meaning (description (index' cs k)) (Data.Mu cs)} ->
          All (description (index' cs k)) (Serialising cs) t ->
          Serialising cs (MkMu k t)
  setMu k layer = MkSerialising $ \ buf, start => goMu buf start k (index' cs k) layer

  export
  setMuK : (cs : Data) -> (k : Fin (length cs)) ->
           {0 t : Meaning (description (index' cs k)) (Data.Mu cs)} ->
           AllK (description (index' cs k)) (Serialising cs) t (Serialising cs (MkMu k t))
  setMuK cs k with (index' cs k)
    _ | cons = SaferIndexed.Data.curry (description cons) $ \ layer =>
               MkSerialising $ \ buf, start => goMu buf start k cons layer


  export
  serialiseToFile : {cs : Data} -> String -> {0 t : Mu cs} ->
                    Serialising cs t -> IO () -- IO (Pointer.Mu cs t) instead?
  serialiseToFile fp t = do
    Just buf <- newBuffer 655360
      | Nothing => failWith "Couldn't allocate buffer"
    end <- setData buf 8 cs
    setInt buf 0 (end - 8)
    size <- runSerialising t buf end
    Right () <- writeBufferToFile fp buf size
      | Left (err, _) => failWith (show err)
    pure ()

namespace Buffer

  setMu : {cs : Data} -> (t : Data.Mu cs) -> Serialising cs t
  setMu (MkMu k t)
    = Serialising.setMu k
    $ all (description (index' cs k)) (assert_total Buffer.setMu) t

  export
  writeToFile : {cs : Data} -> String -> Mu cs -> IO ()
  writeToFile fp t = serialiseToFile fp (setMu t)

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

  public export
  map : (Bits8 -> Bits8) -> Data.Mu Tree -> Data.Mu Tree
  map f = fold $ \ k, v => case k of
    0 => leaf
    1 => let (l, b, r) = v in node l (f b) r

namespace Pointer

  export
  size : {0 t : Data.Mu Tree} -> Pointer.Mu Tree t ->
         IO (Singleton (Data.size t))
  size ptr = case !(out ptr) of
    MkOut 0 t => pure (MkSingleton 0)
    MkOut 1 t => do
      (l # _ # r) <- layer t
      m <- size l
      n <- size r
      pure (S <$> (plus <$> m <*> n))

  export
  sum : {0 t : Data.Mu Tree} ->
        Pointer.Mu Tree t ->
        IO (Singleton (Data.sum t))
  sum ptr = case !(out ptr) of
    MkOut 0 t => pure (MkSingleton 0)
    MkOut 1 t => do
      (l # b # r) <- layer t
      m <- sum l
      n <- sum r
      pure (plus <$> (plus <$> m <*> cast <$> b) <*> n)

  export
  map : (f : Bits8 -> Bits8) ->
        Pointer.Mu Tree t ->
        Serialising Tree (map f t)
  map f ptr = case !(out ptr) of
    MkOut 0 t => setMuK Tree 0
    MkOut 1 t => do
      (l # b # r) <- layer t
      setMuK Tree 1 (map f l) (f <$> b) (map f r)

  export
  display : Pointer.Mu Tree t -> IO String
  display ptr = case !(out ptr) of
    MkOut 0 t => pure "leaf"
    MkOut 1 t => do
      (l # b # r) <- layer t
      l <- display l
      r <- display r
      pure "(node \{l} \{show (getSingleton b)} \{r})"

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


testing : Pointer.Mu Tree t -> IO ()
testing tree = do
  putStrLn "Tree: \{!(display tree)}"
  putStrLn "RSum: \{show !(rsum tree)}"
  putStrLn "Sum: \{show !(sum tree)}"
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
