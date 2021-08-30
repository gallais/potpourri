module Codata.BTree

%default total

public export
record BTree (a : Type) where
  constructor Node
  root  : a
  left  : Inf (BTree a)
  right : Inf(BTree a)

export
unfold : (s -> (a, s, s)) -> s -> BTree a
unfold next seed =
  let (v, lseed, rseed) = next seed in
  Node v (unfold next lseed) (unfold next rseed)

export
Functor BTree where
  map f (Node a l r) = Node (f a) (map f l) (map f r)

export
zipWith : (a -> b -> c) -> BTree a -> BTree b -> BTree c
zipWith f (Node a la ra) (Node b lb rb)
    = Node (f a b) (zipWith f la lb) (zipWith f ra rb)

export
Applicative BTree where
  pure v = t where
    t : BTree a
    t = Node v t t

  Node f lf rf <*> Node x lx rx
    = Node (f x) (lf <*> lx) (rf <*> rx)

public export
data Direction = Left | Right

public export
Path : Type
Path = List Direction

export
step : Direction -> BTree a -> BTree a
step Left  t = t.left
step Right t = t.right

export
index : Path -> BTree a -> a
index [] t = t.root
index (dir :: dirs) t = index dirs (step dir t)
