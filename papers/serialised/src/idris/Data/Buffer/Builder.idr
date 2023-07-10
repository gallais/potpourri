||| A Builder for buffers
||| Rather than allocating a big buffer and hoping it will
||| be enough (and grow it otherwise), provide a Builder
||| interface.

module Data.Buffer.Builder

import Data.Buffer
import Data.Nat
import Data.Singleton

%default total

stringSize : String -> Nat
stringSize = cast . stringByteLength

bufferSize : Buffer  -> Nat
bufferSize buf = cast (unsafePerformIO $ rawSize buf)

------------------------------------------------------------------------
-- Sized builders

data Sized : Nat -> Type where
   Empty : Sized 0
   MkPair : Sized m -> Sized n -> Sized (m + n)
   -- numeric types
   ABits8 : Bits8 -> Sized 1
   ABits16 : Bits16 -> Sized 2
   ABits32 : Bits32 -> Sized 4
   ABits64 : Bits64 -> Sized 8
   AnInt8 : Int8 -> Sized 1
   AnInt16 : Int16 -> Sized 2
   AnInt32 : Int32 -> Sized 4
   AnInt64 : Int64 -> Sized 8
   -- other primitive types
   AString : (str : String) ->
             (m : Singleton (stringSize str)) ->
             Sized (getSingleton m)
   ABuffer : (buf : Buffer) ->
             (m : Singleton (bufferSize buf)) ->
             Sized (getSingleton m)

-- smart constructor
mkPair : Sized m -> Sized n -> Sized (m + n)
mkPair Empty y = y
mkPair x Empty = rewrite plusZeroRightNeutral m in x
mkPair x y = MkPair x y

------------------------------------------------------------------------
-- Builder type and smart constructors

export
record Builder where
  constructor MkBuilder
  {size : Nat}
  getBuilder : Sized size

export
Semigroup Builder where
  MkBuilder x <+> MkBuilder y = MkBuilder (mkPair x y)

export
Monoid Builder where
  neutral = MkBuilder Empty

export %inline
bits8 : Bits8 -> Builder
bits8 = MkBuilder . ABits8

export %inline
bits16 : Bits16 -> Builder
bits16 = MkBuilder . ABits16

export %inline
bits32 : Bits32 -> Builder
bits32 = MkBuilder . ABits32

export %inline
bits64 : Bits64 -> Builder
bits64 = MkBuilder . ABits64

export %inline
int8 : Int8 -> Builder
int8 = MkBuilder . AnInt8

export %inline
int16 : Int16 -> Builder
int16 = MkBuilder . AnInt16

export %inline
int32 : Int32 -> Builder
int32 = MkBuilder . AnInt32

export %inline
int64 : Int64 -> Builder
int64 = MkBuilder . AnInt64

export %inline
string : String -> Builder
string str = MkBuilder (AString str (MkSingleton (stringSize str)))

export %inline
buffer : Buffer -> Builder
buffer str = MkBuilder (ABuffer str (MkSingleton (bufferSize str)))

------------------------------------------------------------------------
-- Running a Builder

export
runBuilder : Builder -> IO (Maybe Buffer)
runBuilder builder = do
  Just buf <- newBuffer (cast $ size builder)
    | Nothing => pure Nothing
  ignore $ assign buf 0 (getBuilder builder)
  pure (Just buf)

  where

  assign : Buffer -> Nat -> Sized m -> IO (Singleton m)
  assign buf pos Empty = pure (MkSingleton 0)
  assign buf pos (MkPair x y)
    = do MkSingleton sx <- assign buf pos x
         MkSingleton sy <- assign buf pos y
         pure (MkSingleton (sx + sy))
  assign buf pos (ABits8 n) = MkSingleton 1 <$ setBits8 buf (cast pos) n
  assign buf pos (ABits16 n) = MkSingleton 2 <$ setBits16 buf (cast pos) n
  assign buf pos (ABits32 n) = MkSingleton 4 <$ setBits32 buf (cast pos) n
  assign buf pos (ABits64 n) = MkSingleton 8 <$ setBits64 buf (cast pos) n
  assign buf pos (AnInt8 n) = MkSingleton 1 <$ setInt8 buf (cast pos) n
  assign buf pos (AnInt16 n) = MkSingleton 2 <$ setInt16 buf (cast pos) n
  assign buf pos (AnInt32 n) = MkSingleton 4 <$ setInt32 buf (cast pos) n
  assign buf pos (AnInt64 n) = MkSingleton 8 <$ setInt64 buf (cast pos) n
  assign buf pos (AString str m@(MkSingleton _))
    = do setString buf (cast pos) str
         pure m
  assign buf pos (ABuffer x m@(MkSingleton _))
    = do copyData x 0 (cast (getSingleton m)) buf (cast pos)
         pure m
