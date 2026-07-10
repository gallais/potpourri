-- Inspired by https://dl.acm.org/doi/10.1145/357766.351253

module Okasaki where

import Control.Monad.Writer
import Data.Monoid

import Problem

data Queue a = Queue
  { front :: [a]
  , back :: [a]
  }

flush :: Queue a -> Queue a
flush (Queue xs ys) = Queue (xs ++ reverse ys) []

pop :: Queue a -> Maybe (a, Queue a)
pop q = case q of
  Queue [] [] -> Nothing
  Queue (hd : tl) r -> Just (hd, Queue tl r)
  _ -> pop (flush q)

top :: Queue a -> Maybe a
top = fmap fst . pop

push :: a -> Queue a -> Queue a
push a (Queue fr bk) = Queue fr (a:bk)

type M a = Writer (Endo (Maybe (Queue (Tree a)))) ()

rebuild :: Problem
rebuild tr = finalise $ tr leaf node where

  finalise :: M a -> Maybe (Tree a)
  finalise = (top =<<) . (`appEndo` (Just $ Queue [] [])) . execWriter

  leaf :: a -> M a
  leaf a = tell $ Endo $ fmap $ push (Leaf a)

  node :: M a
  node = tell $ Endo $ \ mq -> do
    q <- mq
    (a, q) <- pop q
    (b, q) <- pop q
    pure (push (Node b a) q)
