{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module Ref
  ( Ref
  , RefT
  , runRefT
  , newRef
  , readRef
  , writeRef
  , cost
  ) where

import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.State (StateT, get, gets, put, modify, evalStateT, execStateT)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Maybe (fromJust)

import Unsafe.Coerce (unsafeCoerce)

newtype Ref s a = Ref { getRef :: Int }

data Wrapped = forall a. Wrapped a

unsafeUnwrap :: proxy a -> Wrapped -> a
unsafeUnwrap _ (Wrapped v) = unsafeCoerce v

data Store = Store
  { nextAddr :: Int
  , store :: IntMap Wrapped
  }

emptyStore :: Store
emptyStore = Store 0 IntMap.empty

newtype RefT m s a = RefT { getRefT :: StateT Store m a }
  deriving (Functor, Applicative, Monad)

instance MonadIO m => MonadIO (RefT m s) where
  liftIO = RefT . liftIO


runRefT :: Monad m => (forall s. RefT m s a) -> m a
runRefT rma = evalStateT (getRefT rma) emptyStore

cost :: (forall s. RefT Identity s a) -> Int
cost ra = nextAddr $ runIdentity $ execStateT (getRefT ra) emptyStore

newRef :: Monad m => a -> RefT m s (Ref s a)
newRef v = RefT $ do
  Store n st <- get
  put (Store (1+n) $ IntMap.insert n (Wrapped v) st)
  pure (Ref n)

readRef :: Monad m => Ref s a -> RefT m s a
readRef r = RefT $ do
  st <- gets store
  pure $ unsafeUnwrap r $ fromJust (IntMap.lookup (getRef r) st)

writeRef :: Monad m => Ref s a -> a -> RefT m s ()
writeRef r v = RefT $ do
  modify $ \ (Store n st) -> Store n $ IntMap.insert (getRef r) (Wrapped v) st
