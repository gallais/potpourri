module Indexed

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

namespace Data

  parameters {cs : Data nm} (buf : Buffer)

    setMu : Int -> Mu cs -> IO Int
    setMeaning :
      Int ->
      {r : Bool} -> (d : Desc r s n) ->
      Meaning d (Mu cs) ->
      IO (Vect n Int, Int)

    setMu start (MkIndex k # t) with (index k $ constructors cs)
      _ | cons
        = do -- [ Tag | ... offsets ... | t1 | t2 | ... ]
             setBits8 buf start (cast $ cast {to = Nat} k)
             let afterTag  = start + 1
             let afterOffs = afterTag + 8 * cast (offsets cons)
             (is, end) <- setMeaning afterOffs (description cons) t
             setInts buf afterTag is
             pure end

    setMeaning start None v = pure ([], start)
    setMeaning start Byte v = ([], start + 1) <$ setBits8 buf start v
    setMeaning start (Prod d e) (v # w)
      = do (n1, afterLeft) <- setMeaning start d v
           (n2, afterRight) <- setMeaning afterLeft e w
           pure (n1 ++ n2, afterRight)
    setMeaning start {r} Rec v
      = do end <- setMu start v
           pure $ (,end) $ if r then [] else [end - start]

  export
  writeToFile : {cs : Data nm} -> String -> Mu cs -> IO ()
  writeToFile fp mu = do
    Just buf <- newBuffer 655360
      | Nothing => failWith "Couldn't allocate buffer"
    size <- setMu buf 0 mu
    Right () <- writeBufferToFile fp buf size
      | Left (err, _) => failWith (show err)
    pure ()

namespace Pointer

  record Meaning (d : Desc r s n) (cs : Data nm) (t : Meaning d (Data.Mu cs)) where
    constructor MkMeaning
    subterms : Vect n Int
    elemBuffer : Buffer
    elemPosition : Int

  record Mu (cs : Data nm) (t : Data.Mu cs) where
    constructor MkMu
    muBuffer : Buffer
    muPosition : Int

  namespace Poke

    public export
    data Poke' : (d : Desc r s n) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type

    public export
    Poke : (d : Desc r s n) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type
    Poke None _ t = ()
    Poke Byte cs t = Singleton t
    Poke d@(Prod _ _) cs t = Poke' d cs t
    Poke Rec cs t = Pointer.Mu cs t

    data Poke' where
      (#) : Pointer.Meaning d cs t -> Pointer.Meaning e cs u -> Poke' (Prod d e) cs (t # u)

    export
    poke : {0 cs : Data nm} -> {s : Nat} -> (d : Desc r s n) ->
           forall t. Pointer.Meaning d cs t -> IO (Poke d cs t)
    poke None el = pure ()
    poke Byte el = do
      bs <- getBits8 (elemBuffer el) (elemPosition el)
      pure (believe_me $ MkSingleton bs)
    poke (Prod {sl} d e) {t} el = do
      let (n1, n2) = splitAt _ (subterms el)
      let left = MkMeaning n1 (elemBuffer el) (elemPosition el)
      let pos = elemPosition el + sum n1 + cast sl
      let right = MkMeaning n2 (elemBuffer el) pos
      pure $ rewrite etaPair t in (left # right)
    poke Rec el = pure (MkMu (elemBuffer el) (elemPosition el))

  namespace Layer

    public export
    data Layer' : (d : Desc r s n) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type

    public export
    Layer : (d : Desc r s n) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type
    Layer d@(Prod _ _) cs t = Layer' d cs t
    Layer None _ _ = ()
    Layer Byte _ t = Singleton t
    Layer Rec cs t = Pointer.Mu cs t

    data Layer' : (d : Desc r s n) -> (cs : Data nm) -> Data.Meaning d (Data.Mu cs) -> Type where
      (#) : Layer d cs t -> Layer e cs u -> Layer' (Prod d e) cs (t # u)

    export
    layer : {0 cs : Data nm} -> {s : Nat} -> {d : Desc r s n} ->
            forall t. Pointer.Meaning d cs t -> IO (Layer d cs t)
    layer el = poke d el >>= go d where

      go : forall n, r. {s : Nat} -> (d : Desc r s n) ->
           forall t. Poke d cs t -> IO (Layer d cs t)
      go None p = pure ()
      go Byte p = pure p
      go (Prod d e) (p # q) = [| layer p # layer q |]
      go Rec p = pure p

  data Out : (cs : Data nm) -> (t : Data.Mu cs) -> Type where
    (#) : (k : Index cs) ->
          forall t. Pointer.Meaning (description k) cs t ->
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
      (val : Data.Meaning (description k) (Data.Mu cs)
       ** t === (k # val))
    unfoldAs k (l@_ # val) with (decEq k l)
      _ | Yes Refl = (val ** Refl)
      _ | No _ = failWith "The IMPOSSIBLE has happened"

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
      = getOffsets (muBuffer mu) (1 + muPosition mu) (offsets (index k $ constructors cs))
      $ \ subterms, pos => MkMeaning subterms (muBuffer mu) pos

||| Raw sum
rsum : Pointer.Mu Tree t -> IO Nat
rsum ptr = case !(out ptr) of
  0 # el => pure 0
  1 # el => do
    (l # b # r) <- layer el
    pure (!(rsum l) + cast b + !(rsum r))

rightmost : Maybe Bits8 -> Pointer.Mu Tree t -> IO (Maybe Bits8)
rightmost dflt t = case !(out t) of
  0 # el => pure dflt
  1 # el => do
    (_ # b # r) <- layer el
    rightmost (Just (getSingleton b)) r

namespace Data

  public export
  size : Data.Mu Tree -> Nat
  size = fold $ \ k, v => case k of
    0 => 0
    1 => let (l # _ # r) = v in S (l + r)

  public export
  sum : Data.Mu Tree -> Nat
  sum = fold $ \ k, v => case k of
    0 => 0
    1 => let (l # b # r) = v in l + cast b + r

namespace Pointer

  export
  size : {0 t : Data.Mu Tree} -> Pointer.Mu Tree t ->
         IO (Singleton (Data.size t))
  size ptr = case !(out ptr) of
    0 # el => pure (MkSingleton 0)
    1 # el => do
      (l # _ # r) <- layer el
      m <- size l
      n <- size r
      pure (S <$> (plus <$> m <*> n))

  sum : {0 t : Data.Mu Tree} ->
        Pointer.Mu Tree t ->
        IO (Singleton (Data.sum t))
  sum ptr = case !(out ptr) of
    0 # el => pure (MkSingleton 0)
    1 # el => do
      (l # b # r) <- layer el
      m <- sum l
      n <- sum r
      pure (plus <$> (plus <$> m <*> cast <$> b) <*> n)

||| initFromFile creates a pointer to a datastructure stored in a file
||| @ cs is the datatype you want to use to decode the buffer's content
initFromFile : (cs : Data nm) -> String -> IO (Exists (Pointer.Mu cs))
initFromFile cs fp
  = do Right buf <- createBufferFromFile fp
         | Left err => failWith (show err)
       pure (Evidence t (MkMu buf 0))
  where 0 t : Data.Mu cs -- postulated as an abstract value

main : IO ()
main = do
  writeToFile "tmp" example
  Evidence _ tree <- initFromFile Tree "tmp"
  putStrLn "RSum: \{show !(rsum tree)}"
  putStrLn "Sum: \{show !(sum tree)}"
  putStrLn "Rightmost: \{show !(rightmost Nothing tree)}"
  putStrLn "Tree size: \{show !(size tree)}"
