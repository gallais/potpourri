{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}

module Solution where

------------------------------------------------------------------------
-- Core idea

-- This solution is based on the geometric intuition that at any point
-- in the breadth first traversal, we have traversed a tree-shaped
-- prefix of a tree with holes at the leaves.
--
-- These holes correspond to the subtrees we have yet to visit. And
-- we know, by definition of breadth-first, that we will visit them
-- left-to-right.
--
-- Visiting a leaf fills the corresponding hole with said leaf.
-- Visiting a node fills the corresponding hole with a node whose
-- two subtrees are both fresh holes who will be filled in later
-- when the breadth-first algorithm has circled back to them.
--
------------------------------------------------------------------------

import Control.Applicative ((<|>))
import Control.Monad.State (State, execState, modify)

import Problem

-- First, a few instances we are interested in

deriving instance Functor Tree
deriving instance Foldable Tree
deriving instance Traversable Tree

------------------------------------------------------------------------
-- Positions in trees

-- In order to identify a hole in context, we define contexts and
-- the notion of a (sub)tree in focus.

-- An inside-out context one-hole C[_] whose meaning
-- is described by the implementation of plug below.
data Context a
  = Top
  | LeftOf (Context a) (Tree a)
  | RightOf (Tree a) (Context a)

data Focus a = Focus
  { context :: Context a
  , inFocus :: Tree a
  }

-- Given (C[_], t) return C[t]
plug :: Focus a -> Tree a
plug (Focus c t) = go c t where

  go Top t = t
  go (LeftOf c r) t = go c (Node t r)
  go (RightOf l c) t = go c (Node l t)

------------------------------------------------------------------------
-- Navigating trees with holes

-- We represent a tree with leaves that either contain a value
-- of type a or a hole as a tree of (Maybe a) values

pattern Hole = Leaf Nothing

-- Find the next hole to the right of the current focus,
-- wrapping around to the left side if necessary.
nextHole
  :: Focus (Maybe a)
  -> Maybe (Focus (Maybe a))
nextHole (Focus c t) = search c t

  where

    -- Look for the leftmost hole in the tree in focus
    -- (not touching the context)
    local c Hole = Just (Focus c Hole)
    local c (Leaf _) = Nothing
    local c (Node l r) = local (LeftOf c r) l <|> local (RightOf l c) r

    -- Look for a hole to the right of the current tree in focus,
    -- going back up in the tree if necessary.
    search Top t = local Top t
    search (LeftOf c r) t = local (RightOf t c) r <|> search c (Node t r)
    search (RightOf l c) t = search c (Node l t)

------------------------------------------------------------------------
-- Rebuilding a tree from its breadth-first traversal

type S a = Maybe (Focus (Maybe a))

rebuild :: Problem
rebuild tr = finalise (tr leaf node) where

  -- Kickstart the computation with a hole in topmost position
  -- By the time we are done and have plugged the focus back together,
  -- all the holes better be gone!
  finalise :: State (S a) () -> Maybe (Tree a)
  finalise act = do
    f <- execState act (Just $ Focus Top Hole)
    sequence (plug f)

  -- If the traversal is reporting a leaf then we should have
  -- a hole to the right of us and we can fill it.
  leaf :: a -> State (S a) ()
  leaf a = modify $ \ mf -> do
    f <- mf
    f <- nextHole f
    pure (f { inFocus = Leaf (Just a) })

  -- If the traversal has spotted a node, there better be a hole
  -- for us to instantiate with a Node with two holes for subtrees.
  node :: State (S a) ()
  node = modify $ \ mf -> do
    f <- mf
    f <- nextHole f
    pure (f { inFocus = Node Hole Hole })
