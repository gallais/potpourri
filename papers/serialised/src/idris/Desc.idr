module Desc

import Data.Fin
import Data.Vect
import Data.Buffer
import System.File.Buffer

import Lib
import Serialised.Desc

%default total

namespace Data

  parameters {ds : Data nm} (buf : Buffer)

    muToBuffer : Int -> Mu ds -> IO Int
    elemToBuffer :
      Int ->
      {r : Bool} -> (d : Desc r s n) ->
      Meaning d (Mu ds) ->
      IO (Vect n Int, Int)

    muToBuffer start (MkIndex k # t) with (index k $ constructors ds)
      _ | cons = do -- [ Tag | ... offsets ... | t1 | t2 | ... ]
                    setBits8 buf start (cast $ cast {to = Nat} k)
                    let afterTag  = start + 1
                    let afterOffs = afterTag + 8 * cast (offsets cons)
                    (is, end) <- elemToBuffer afterOffs (description cons) t
                    setInts buf afterTag is
                    pure end

    elemToBuffer start None v = pure ([], start)
    elemToBuffer start Byte v = ([], start + 1) <$ setBits8 buf start v
    elemToBuffer start (Prod d e) (v # w)
      = do (n1, afterLeft) <- elemToBuffer start d v
           (n2, afterRight) <- elemToBuffer afterLeft e w
           pure (n1 ++ n2, afterRight)
    elemToBuffer start {r} Rec v
      = do end <- muToBuffer start v
           pure $ (,end) $ if r then [] else [end - start]

  export
  writeToFile : {ds : Data nm} -> String -> Mu ds -> IO ()
  writeToFile fp mu = do
    Just buf <- newBuffer 655360
      | Nothing => failWith "Couldn't allocate buffer"
    size <- muToBuffer buf 0 mu
    Right () <- writeBufferToFile fp buf size
      | Left (err, _) => failWith (show err)
    pure ()

namespace Pointer

  record Meaning (d : Desc r s n) (cs : Data nm) where
    constructor MkMeaning
    subterms : Vect n Int
    elemBuffer : Buffer
    elemPosition : Int

  record Mu (cs : Data nm) where
    constructor MkMu
    muBuffer : Buffer
    muPosition : Int

  Poke : (d : Desc r s n) -> (cs : Data nm) -> Type
  Poke None _ = ()
  Poke Byte cs = Bits8
  Poke (Prod d e) cs = (Pointer.Meaning d cs, Pointer.Meaning e cs)
  Poke Rec cs = Pointer.Mu cs

  poke : {s : Nat} -> (d : Desc r s n) ->
         Pointer.Meaning d cs -> IO (Poke d cs)
  poke None el = pure ()
  poke Byte el = getBits8 (elemBuffer el) (elemPosition el)
  poke (Prod {sl} d e) el = do
    let (n1, n2) = splitAt _ (subterms el)
    let left = MkMeaning n1 (elemBuffer el) (elemPosition el)
    let pos = elemPosition el + sum n1 + cast sl
    let right = MkMeaning n2 (elemBuffer el) pos
    pure (left, right)
  poke Rec el = pure (MkMu (elemBuffer el) (elemPosition el))

  Layer : (d : Desc r s n) -> (cs : Data nm) -> Type
  Layer None cs = ()
  Layer Byte cs = Bits8
  Layer (Prod d e) cs = (Layer d cs, Layer e cs)
  Layer Rec cs = Pointer.Mu cs

  layer : {s : Nat} -> (d : Desc r s n) ->
          Pointer.Meaning d cs -> IO (Layer d cs)
  layer d el = poke d el >>= go d where

    go : forall n, r. {s : Nat} -> (d : Desc r s n) -> Poke d cs -> IO (Layer d cs)
    go None p = pure p
    go Byte p = pure p
    go (Prod d e) (p, q) = [| (layer d p, layer e q) |]
    go Rec p = pure p

  record Out (cs : Data nm) where
    constructor MkOut
    choice : Index cs
    encoding : Pointer.Meaning (description choice) cs

  out : {cs : _} -> Pointer.Mu cs -> IO (Out cs)
  out mu = do
    tag <- getBits8 (muBuffer mu) (muPosition mu)
    let Just choice = natToFin (cast tag) (consNumber cs)
      | _ => failWith "Invalid representation"
    MkOut (MkIndex choice) <$> getConstructor (index choice $ constructors cs) mu

    where

    getOffsets : Buffer -> Int -> -- Buffer & position
                 (n : Nat) ->
                 (Vect n Int -> Int -> Pointer.Meaning d cs) ->
                 IO (Pointer.Meaning d cs)
    getOffsets buf pos 0 k = pure (k [] pos)
    getOffsets buf pos (S n) k = do
      off <- getInt buf pos
      getOffsets buf (8 + pos) n (k . (off ::))

    getConstructor : (c : Constructor _) ->
      Pointer.Mu cs -> IO (Pointer.Meaning (description c) cs)
    getConstructor c mu
      = getOffsets (muBuffer mu) (1 + muPosition mu) (offsets c)
      $ \ subterms, pos => MkMeaning subterms (muBuffer mu) pos


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
    | Left err => failWith (show err)
  let tree : Pointer.Mu Tree = MkMu buf 0
  val <- sum tree
  putStrLn "Sum: \{show val}"
