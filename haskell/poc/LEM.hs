{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE UndecidableInstances       #-}

module LEM ( LEMT
           , LEM
           , lem
           , liftLEMT
           , execLEMT
           , execLEM
           ) where

import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Dynamic
import Data.Either
import Data.Proxy
import Data.Void

-- | Law of Excluded Middle Monad Transformer
--
--   We use a phantom type @s@ to make sure that LEM guesses are not allowed to
--   escape their scope (cf. the type of the continuation in @lem@ and that of
--   @execLEMT@).
--
--   We will always give an a priori negative answer and use an @ExceptT Backtrack@
--   to change our mind if the user provides us with some evidence that we have made
--   a mistake.
--
--   We use a @ReaderT Integer@ to tag our calls to @lem@. This way when we get a
--   @Backtrack@ we know to which calls it corresponds to and we can unwrap the
--   @Dynamic@ evidence provided to us.

type LEM (s :: [*]) = LEMT s Identity
newtype LEMT (s :: [*]) m a = LEMT { runLEMT :: ReaderT Integer (ExceptT Backtrack m) a }
  deriving (Functor, Applicative, Monad, MonadError Backtrack, MonadReader Integer, MonadIO)

data Backtrack = Backtrack Integer Dynamic

-- | @lem@ evaluates the continuation with a negative answer in an environment where
--   the tags have been incremented by one.
--   If the user tries to use that negative information, they must provide us with
--   evidence which we promptly return in a @Backtrack@. We recover from the error
--   by restarting the continuation with a positive answer using the evidence we
--   were just provided.

lem :: forall a b ss m. (Monad m, Typeable a, NFData a, NFData b) =>
       (forall s. Either a (a -> LEMT (s ': ss) m Void) -> LEMT (s ': ss) m b) -> LEMT ss m b
lem k = LEMT $ do
  i <- ask
  local (const (i+1)) (runLEMT $ k $ Right $ \ a -> rnf a `seq` throwError (Backtrack i $ toDyn a))
   `catchError` \ e -> case e of
-- It is crucial here to make sure that the @Backtrack@ we get corresponds to this
-- use of @lem@. Otherwise the call to @fromDyn@ would probably fail to typecheck.
-- If we are talking about an earlier call, we propagate the @Backtrack@ by re-throwing
-- the error.
      Backtrack i' v | i == i' -> runLEMT $ k (Left $ fromDyn v undefined)
      _ -> throwError e

execLEMT :: Functor m => (forall s. LEMT s m a) -> m a
execLEMT = fmap (fromRight undefined)
         . runExceptT
         . flip runReaderT 0
         . runLEMT

execLEM :: (forall s. LEM s a) -> a
execLEM k = runIdentity (execLEMT k)


example :: forall s. LEMT s IO Integer
example = lem $ \ o -> case o of
  Left v     -> liftIO (putStrLn "first") >> pure v
  Right notv -> lem $ \ o -> case o of
    Left w     -> liftIO (putStrLn "second") >> absurd <$> (liftLEMT $ notv (4 + w))
    Right notw -> absurd <$> notw 3
--    Right notw -> absurd <$> liftLEMT (notv 3)

{-
example2 :: forall s. LEMT s IO Integer
example2 = do
  o <- lem pure -- type error!
  case o of
    Left v     -> pure v
    Right notv -> absurd <$> notv 3
-}

-- | @liftLEMT@ lets us use a LEM-obtained result in an extended context,
--   i.e. haver having called @lem@ at least one more time.

liftLEMT :: forall s t m a. LT s t ~ True => LEMT s m a -> LEMT t m a
liftLEMT = LEMT . runLEMT

type family EQ x y where
  EQ x x = 'True
  EQ x y = 'False

type family OR (b :: Bool) (c :: Bool) where
  OR 'True c  = 'True
  OR b 'True  = 'True
  OR b 'False = b
  OR 'False c = c

type family LT (xs :: [k]) (ys :: [k]) where
  LT xs (h ': ys) = LE xs ys
  LT xs ys        = 'False

type family LE (g :: [k]) (h :: [k]) where
  LE xs ys = OR (EQ xs ys) (LT xs ys)
