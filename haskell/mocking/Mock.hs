{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

-- The content of this file is inspired by the paper
-- Beauty in the Beast — A Functional Semantics for the Awkward Squad
-- by Wouter Swierstra Thorsten Altenkirch

module Mock where

import Control.Monad.IO.Class (MonadIO(liftIO))

import Data.Foldable (forM_)
import Data.Maybe (catMaybes)
import Data.Traversable (forM)

import Ref (Ref, RefT, cost)
import qualified Ref
import Data.IORef

------------------------------------------------------------------------
-- Model

class Monad m => MonadRef ref m | m -> ref where
  newRef :: a -> m (ref a)
  readRef :: ref a -> m a
  writeRef :: ref a -> a -> m ()

data Data ref = Cell Int (ref (Data ref)) | NULL

deriving instance Show (ref (Data ref)) => Show (Data ref)

type Queue ref = (ref (Data ref), ref (Data ref))

------------------------------------------------------------------------
-- Generic implementations

emptyQueue :: MonadRef ref m => m (Queue ref)
emptyQueue = do
  front <- newRef NULL
  back <- newRef NULL
  pure (front, back)

enqueue :: MonadRef ref m => Queue ref -> Int -> m ()
enqueue (front, back) i = do
  end <- Cell i <$> newRef NULL
  d <- readRef back
  writeRef back end
  case d of
    NULL -> writeRef front end
    Cell _ next -> writeRef next end

dequeue :: MonadRef ref m => Queue ref -> m (Maybe Int)
dequeue (front, back) = do
  df <- readRef front
  case df of
    NULL -> pure Nothing
    Cell i newFront -> Just i <$ do
      dn <- readRef newFront
      writeRef front dn
      -- don't forget to nullify back if we have reached the end
      -- (bug in the original paper!)
      case dn of
        NULL -> writeRef back NULL
        _ -> pure ()

reverseQueue :: MonadRef ref m => Queue ref -> m ()
reverseQueue (front, back) = readRef front >>= \case
  NULL -> pure ()
  d@_ -> do
    flipPointers NULL d
    b <- readRef back
    writeRef front b
    writeRef back d

  where

    flipPointers :: MonadRef ref m => Data ref -> Data ref -> m ()
    flipPointers _ NULL = pure ()
    flipPointers d d'@(Cell _ next) = do
      d'' <- readRef next
      writeRef next d
      flipPointers d' d''

fromList :: MonadRef ref m => [Int] -> m (Queue ref)
fromList is = do
  q <- emptyQueue
  q <$ forM_ is (enqueue q)


------------------------------------------------------------------------
-- Generic test function

test :: (MonadIO m, MonadRef ref m) => Int -> m (Queue ref)
test n = do
  q <- fromList [1..n]
  reverseQueue q
  is1 <- forM [1..n] (const $ dequeue q)
  forM_ [1..n] (enqueue q)
  reverseQueue q
  reverseQueue q
  is2 <- forM [1..n] (const $ dequeue q)
  liftIO $ print $ catMaybes is1
  liftIO $ print $ catMaybes is2
  pure q

------------------------------------------------------------------------
-- Instances

instance MonadRef IORef IO where
  newRef = newIORef
  readRef = readIORef
  writeRef = writeIORef

instance Monad m => MonadRef (Ref s) (RefT m s) where
  newRef = Ref.newRef
  readRef = Ref.readRef
  writeRef = Ref.writeRef

test' :: Int -> IO ()
test' n = Ref.runRefT (() <$ test n)

noAlloc :: (forall ref m. MonadRef ref m => Queue ref -> m ()) -> Bool
noAlloc act
  = cost (() <$ fromList [1..100]) == cost (act =<< fromList [1..100])
