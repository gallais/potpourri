{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}

module Solution where

import Control.Applicative ((<|>))
import Control.Monad.State (State, execState, modify)

import Problem

deriving instance Functor Tree
deriving instance Foldable Tree
deriving instance Traversable Tree

data Context a
  = Top
  | LeftOf (Context a) (Tree a)
  | RightOf (Tree a) (Context a)

data Focus a = Focus
  { context :: Context a
  , inFocus :: Tree a
  }

plug :: Focus a -> Tree a
plug (Focus c t) = go c t where

  go Top t = t
  go (LeftOf c r) t = go c (Node t r)
  go (RightOf l c) t = go c (Node l t)

pattern Hole = Leaf Nothing

nextHole
  :: Focus (Maybe a)
  -> Maybe (Focus (Maybe a))
nextHole (Focus c t) = up c t

  where

    local c Hole = Just (Focus c Hole)
    local c (Leaf _) = Nothing
    local c (Node l r) = local (LeftOf c r) l <|> local (RightOf l c) r

    up Top t = local Top t
    up (LeftOf c r) t = local (RightOf t c) r <|> up c (Node t r)
    up (RightOf l c) t = up c (Node l t)

type S a = Maybe (Focus (Maybe a))

rebuild :: Problem
rebuild tr = finalise (tr leaf node) where

  finalise :: State (S a) () -> Maybe (Tree a)
  finalise act = do
    f <- execState act (Just $ Focus Top Hole)
    sequence (plug f)

  leaf :: a -> State (S a) ()
  leaf a = modify $ \ mf -> do
    f <- mf
    f <- nextHole f
    pure (f { inFocus = Leaf (Just a) })

  node :: State (S a) ()
  node = modify $ \ mf -> do
    f <- mf
    f <- nextHole f
    pure (f { inFocus = Node Hole Hole })
