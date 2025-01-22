module ParReq

import Data.Linear.LVect
import Data.Vect

import Control.Linear.LIO
import System.Concurrency
import System.Concurrency.Linear

%default total

namespace Shape

  public export
  data Shape : Type where
    Leaf : Nat -> Shape
    Node : Shape -> Shape -> Shape

namespace Tree

  public export
  data Tree : Shape -> Type -> Type where
    Leaf : Vect n a -> Tree (Leaf n) a
    Node : Tree s1 a -> Tree s2 a -> Tree (Node s1 s2) a

  export
  Functor (Tree shp) where
    map f (Leaf xs) = Leaf (map f xs)
    map f (Node l r) = Node (map f l) (map f r)

  export
  Foldable (Tree shp) where
    foldr c n (Leaf xs) = foldr c n xs
    foldr c n (Node l r) = foldr c (foldr c n r) l

  export
  Traversable (Tree shp) where
    traverse f (Leaf xs) = Leaf <$> traverse f xs
    traverse f (Node l r) = Node <$> traverse f l <*> traverse f r

export
data Req : (i, o : Type) -> Type -> Type where
  Pure : a -> Req i o a
  Call : Tree shp i -> (Tree shp o -> Req i o a) -> Req i o a

interface Functor1 f1 where
  map1 : (a -@ b) -> f1 a -@ f1 b

interface Functor1 f1 => Applicative1 f1 where
  pure1 : a -@ f1 a
  ap1 : f1 (a -@ b) -@ f1 a -@ f1 b

export
calls : Vect n i -> Req i o (Vect n o)
calls is = Call (Leaf is) (\ (Leaf os) => Pure os)

export
call : i -> Req i o o
call i = Call (Leaf [i]) (\ (Leaf [o]) => Pure o)

export
Functor (Req i o) where
  map f (Pure x) = Pure (f x)
  map f (Call is ks) = Call is (map f . ks)

export
Applicative (Req i o) where
  pure = Pure
  Pure f <*> r = map f r
  r <*> Pure x = map ($ x) r
  Call is1 ks1 <*> Call is2 ks2
    = Call (Node is1 is2) (\ (Node os1 os2) => ks1 os1 <*> ks2 os2)

export
Monad (Req i o) where
  Pure x >>= f = f x
  Call is ks >>= f = Call is ((>>= f) . ks)

export
concurrently : L IO a -@ L1 IO (L IO a)
concurrently act = do
  ch <- makeChannel
  _ <- fork1 $ do
    x <- act
    channelPut ch x
  pure1 $ channelGet ch

namespace LVect

  export
  ltraverse :
    LinearBind io =>
    (a -> L1 io b) -> Vect n a -> L1 io (LVect n b)
  ltraverse f [] = pure1 []
  ltraverse f (a :: as) = do
    b <- f a
    bs <- ltraverse f as
    pure1 (b :: bs)

  export
  traverseL :
    LinearBind io => Applicative io =>
    (a -@ L io b) -> LVect n a -@ L io (Vect n b)
  traverseL f [] = pure []
  traverseL f (a :: as) = do
    b <- f a
    bs <- traverseL f as
    pure (b :: bs)

namespace LTree

  public export
  data LTree : Shape -> Type -> Type where
    Leaf : LVect n a -@ LTree (Leaf n) a
    Node : LTree s1 a -@ LTree s2 a -@ LTree (Node s1 s2) a

  export
  ltraverse :
    LinearBind io =>
    (a -> L1 io b) -> Tree n a -> L1 io (LTree n b)
  ltraverse f (Leaf as) = do
    as <- LVect.ltraverse f as
    pure1 (Leaf as)
  ltraverse f (Node l r) = do
    l <- LTree.ltraverse f l
    r <- LTree.ltraverse f r
    pure1 (Node l r)

  export
  traverseL :
    LinearBind io => Applicative io =>
    (a -@ L io b) -> LTree n a -@ L io (Tree n b)
  traverseL f (Leaf as) = do
    as <- LVect.traverseL f as
    pure (Leaf as)
  traverseL f (Node l r) = do
    l <- traverseL f l
    r <- traverseL f r
    pure (Node l r)

export
runReq : (i -> L IO o) -> Req i o a -> L IO a
runReq f (Pure x) = pure x
runReq f (Call is ks) = do
  -- fork all the requests
  recvs <- LTree.ltraverse (\ i => concurrently (f i)) is
  -- wait for all the replies
  os <- LTree.traverseL id recvs
  -- continue
  runReq f (ks os)
