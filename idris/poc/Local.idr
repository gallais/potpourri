module Local

import Data.List

%default total

data Desc : Type where
  AnInt, ARec: Desc
  ASum, AProd : List Desc -> Desc

namespace Serialised

  record Elem (d, x : Desc) where
    constructor MkElem
    runElem : AnyPtr

  deref : AnyPtr -> IO Int
  offset : AnyPtr -> Int -> AnyPtr
  sizeOfInt : Nat

  Mu : Desc -> Type
  Mu d = Elem d d

  Head : (d, x : Desc) -> Type
  Head AnInt x = Int
  Head ARec x = Mu x
  Head (ASum ds) x = ?A
  Head (AProd []) x = ()
  Head (AProd (d :: [])) x = Elem d x
  Head (AProd (d :: ds@(_ :: _))) x = (Elem d x, Elem (AProd ds) x)

  head : (d : Desc) -> Elem d x -> IO (Head d x)
  heads : (d : Desc) -> Elem (AProd (d :: ds)) x -> IO (Elem d x, Elem (AProd ds) x)


  head AnInt ptr = deref (runElem ptr)
  head ARec ptr = pure (believe_me ptr)
  head (ASum ds) ptr
    = do let raw = runElem ptr
         tag <- deref raw
         let ptr = offset raw (cast sizeOfInt)
         case inBounds (cast tag) ds of
           No contra => assert_total $ idris_crash "invalid serialised data"
           Yes prf => ?a_0

  head (AProd []) ptr = pure ()
  head (AProd (d :: [])) ptr = pure (believe_me ptr)
  head (AProd (d :: ds@(_ :: _))) ptr = heads d ptr

  heads AnInt ptr = do
    let raw1 = runElem ptr
    let raw2 = offset raw1 (cast sizeOfInt)
    pure (MkElem raw1, MkElem raw2)
  heads d ptr = do
    let raw = runElem ptr
    size <- deref raw
    let raw1 = offset raw (cast sizeOfInt)
    let raw2 = offset raw1 size
    pure (MkElem raw1, MkElem raw2)
