module Problem where

data Tree a
  = Leaf a
  | Node (Tree a) (Tree a)
  deriving (Show, Eq)

data SnocList a = SNil | (:<) (SnocList a) a

(<>>) :: SnocList a -> [a] -> [a]
SNil <>> as = as
(sa :< a) <>> as = sa <>> (a : as)

type TreeTraversal a =
  forall m. Applicative m
  => (a -> m ())
  -> m ()
  -> m ()

breadthFirst :: Tree a -> TreeTraversal a
breadthFirst t leaf node = go SNil [t] where

  go SNil [] = pure ()
  go next [] = go SNil (next <>> [])
  go next (t : ts) = case t of
    Leaf a -> leaf a *> go next ts
    Node l r -> node *> go (next :< l :< r) ts

type Problem = forall a. TreeTraversal a -> Maybe (Tree a)

-- Challenge:
-- write rebuild :: Problem
-- such that rebuild (breadthFirst t) == Just t
