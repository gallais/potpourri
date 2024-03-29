module Data.Serialisable.SafeFolds

import Lib
import Data.Serialisable.Desc
import Data.Serialisable.Data
import Data.Serialisable.Pointer

import Data.Singleton

%hide Data.fold
%hide Pointer.fold

%default total

parameters {cs : Data nm} (alg : Alg cs a)

  fold : Data.Mu cs -> a
  fmapFold : (d : Desc{}) -> Data.Meaning d (Data.Mu cs) -> Data.Meaning d a

  fold (k # t) = alg k (fmapFold (description k) t)

  fmapFold None t = t
  fmapFold Byte t = t
  fmapFold (Prod d e) (s # t)
    = (fmapFold d s # fmapFold e t)
  fmapFold Rec t = fold t

namespace Pointer

  parameters {cs : Data nm} (alg : Alg cs a)

    fold : Pointer.Mu cs t -> IO (Singleton (fold alg t))
    fmapFold : (d : Desc{}) -> forall t. Pointer.Meaning d cs t ->
               IO (Singleton (fmapFold alg d t))

    fold ptr
      = do k # t <- out ptr
           rec <- fmapFold (description k) t
           pure (alg k <$> rec)

    fmapFold d ptr = poke ptr >>= go d where

      go : (d : Desc{}) -> forall t. Poke d cs t -> IO (Singleton (fmapFold alg d t))
      go None {t} v = rewrite etaUnit t in pure (pure ())
      go Byte v = pure v
      go (Prod d e) (v # w)
        = do v <- fmapFold d v
             w <- fmapFold e w
             pure [| v # w |]
      go Rec v = fold v
