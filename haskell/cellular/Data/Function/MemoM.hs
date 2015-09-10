module Data.Function.MemoM (memoM) where

import Data.Map.Strict as Map
import Data.IORef
import System.IO.Unsafe

memoM :: (Ord k, Monad m) => (k -> m v) -> (k -> m v)
memoM =
  let ref = unsafePerformIO $ newIORef empty in
  ref `seq` loopM ref

loopM :: (Ord k, Monad m) => IORef (Map k v) -> (k -> m v) -> (k -> m v)
loopM ref f k =
  let m = unsafePerformIO (readIORef ref) in
  case Map.lookup k m of
    Just v  -> return v
    Nothing -> do
      v <- f k
      let upd = unsafePerformIO (writeIORef ref $ insert k v m)
      upd `seq` return v
