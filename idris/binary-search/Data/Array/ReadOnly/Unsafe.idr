module Data.Array.ReadOnly.Unsafe

import Data.Array.ReadOnly
import Data.DPair

export
unsafeReadValue : (HasIO io, Storable a) =>
  (arr : Array a) -> (i : Int) -> io (Subset a (ValueAt arr i))
unsafeReadValue arr i = map (\ v => Element v MkValueAt) $ unsafeGetValueAt arr i
