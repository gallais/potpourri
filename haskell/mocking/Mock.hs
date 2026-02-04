{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

-- The content of this file is inspired by the paper
-- Beauty in the Beast — A Functional Semantics for the Awkward Squad
-- by Wouter Swierstra Thorsten Altenkirch

module Mock where

import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO(liftIO))

import Data.Foldable (forM_)
import Data.Kind (Type)
import Data.Maybe (catMaybes, fromJust)
import Data.Traversable (forM)

import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.State (StateT, get, put, modify, runStateT, execStateT)
import Data.IORef
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

------------------------------------------------------------------------
-- Model

class Monad m =>
  MonadRef
    (ref :: Type -> Type)
    (m :: Type -> Type)
    | m -> ref where
  newRef   :: Data ref -> m (ref (Data ref))
  readRef  :: ref (Data ref) -> m (Data ref)
  writeRef :: ref (Data ref) -> Data ref -> m ()

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
enqueue (front, back) i = readRef back >>= \case
  NULL -> do
    end <- newRef NULL
    writeRef front (Cell i end)
    writeRef back (Cell i end)
  Cell _ end -> do
    newEnd <- newRef NULL
    writeRef end (Cell i newEnd)
    writeRef back (Cell i newEnd)

dequeue :: MonadRef ref m => Queue ref -> m (Maybe Int)
dequeue (front, back) = do
  d <- readRef front
  case d of
    NULL -> pure Nothing
    Cell i newFront -> Just i <$ do
      d <- readRef newFront
      writeRef front d
      case d of
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
    flipPointers d NULL = pure ()
    flipPointers d d'@(Cell i next) = do
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

newtype Addr a = MkAddr { getAddr :: Int } deriving Show

data Store = MkStore
  { nextAddr :: Int
  , store :: IntMap (Data Addr)
  } deriving (Show)

emptyStore :: Store
emptyStore = MkStore 0 IntMap.empty

instance Monad m => MonadRef Addr (StateT Store m) where
  newRef v = do
    MkStore r store <- get
    put $ MkStore (r + 1) (IntMap.insert r v store)
    pure (MkAddr r)
  readRef (MkAddr r) = fromJust . IntMap.lookup r . store <$> get
  writeRef (MkAddr r) v = do
    modify (\ (MkStore n s) -> MkStore n (IntMap.insert r v s))

test' :: Int -> IO (Queue Addr, Store)
test' n = runStateT (test n) emptyStore


cost :: StateT Store Identity a -> Int
cost act
  = nextAddr
  $ runIdentity
  $ flip execStateT emptyStore
  $ act

noAlloc :: (forall ref m. MonadRef ref m => Queue ref -> m ()) -> Bool
noAlloc act
  = cost (fromList [1..100])  == cost (act =<< fromList [1..100])
