module Data.Serialisable.Tree

import Control.Monad.State

import Data.List1
import Data.Singleton
import Data.String
import Data.Vect

import Lib

import Data.Serialisable.Desc
import Data.Serialisable.Data
import Data.Serialisable.Pointer

------------------------------------------------------------------------
-- Definition of the datatype: data Tree = Leaf | Node Tree Word8 Tree
-- and pattern synonyms

public export
Leaf : Constructor String
Leaf = "Leaf" :: None

public export
Node : Constructor String
Node = "Node" :: Prod Rec (Prod Byte Rec)

public export
Tree : Data String
Tree = MkData [Leaf, Node]

public export
ATree : Type
ATree = Data.Mu Tree

------------------------------------------------------------------------
-- Smart constructors and examples

public export
leaf : ATree
leaf = "Leaf" # ()

public export
node : ATree -> Bits8 -> ATree -> ATree
node l b r = "Node" # l # b # r

export
full : (n : Nat) -> ATree
full = evalState 0 . go where

  tick : State Nat Bits8
  tick = do
    n <- get
    put (S n)
    pure (cast n)

  go : (n : Nat) -> State Nat ATree
  go 0 = pure leaf
  go (S k) = node <$> go k <*> tick <*> go k

public export
example : ATree
example =
  (node
    (node (node leaf 1 leaf) 5 leaf)
    10
    (node leaf 20 leaf))

public export
bigexample : ATree
bigexample =
  (node
    (node (node leaf 1 leaf) 5 leaf)
    10
    (node leaf 20
      (node
        (node leaf 56 (node leaf 5 leaf))
        17
        (node leaf 23
          (node leaf 78 leaf)))))

------------------------------------------------------------------------
-- Fancy show function

export
showi : String -> Mu Tree -> String
showi pad t = unlines (let (hd ::: tl) = go 0 pad t [] in (pad ++ hd) :: tl) where

  go : Nat -> String -> Mu Tree -> List String -> List1 String
  go closings pad ("Leaf" # _) acc = ("leaf" ++ replicate closings ')') ::: acc
  go closings pad ("Node" # ("Leaf" # _) # b # ("Leaf" # _)) acc
    = (unwords ("(node" :: "leaf" :: show b :: "leaf" :: []) ++ replicate (S closings) ')') ::: acc
  go closings pad ("Node" # l # b # r) acc
    = let pad = "      " ++ pad in
      let hd₁ ::: tl₁ = go (S closings) pad r acc in
      let byte = pad ++ show b in
      let hd₂ ::: tl₂ = go 0 pad l $ byte :: (pad ++ hd₁) :: tl₁ in
      ("(node " ++ hd₂) ::: tl₂

export
show : Mu Tree -> String
show = showi ""


------------------------------------------------------------------------
-- Pure versions of the functions

namespace Data

  ||| Find a byte
  public export
  find : Bits8 -> Data.Mu Tree -> Bool
  find tgt t = case t of
    "Leaf" # _ => False
    "Node" # l # b # r => b == tgt || find tgt l || find tgt r

  ||| Tree sum
  public export
  sum : Data.Mu Tree -> Nat
  sum t = case t of
    "Leaf" # _ => 0
    "Node" # l # b # r =>
      let m = sum l
          n = sum r
      in (m + cast b + n)

  public export
  leftBranch : Data.Mu Tree -> Data.Mu Tree
  leftBranch ("Node" # l # _ # _) = l
  leftBranch t = t

  public export
  rightBranch : Data.Mu Tree -> Data.Mu Tree
  rightBranch ("Node" # _ # _ # r) = r
  rightBranch t = t

  public export
  rightmost : ATree -> Maybe Bits8
  rightmost t = case t of
    "Leaf" # _ => Nothing
    "Node" # l # b # r => Just (fromMaybe b (rightmost r))

  public export
  swap : Data.Mu Tree -> Data.Mu Tree
  swap ("Leaf" # _) = "Leaf" # ()
  swap ("Node" # l # b # r) = "Node" # r # b # l

  ||| Map is obtained by applying a function transforming Bit8 values
  ||| to all of the Bits8 stored in the tree's nodes
  public export
  map : (Bits8 -> Bits8) -> Data.Mu Tree -> Data.Mu Tree
  map f = fold $ \ k, v => case k of
    "Leaf" => leaf
    "Node" => let (l # b # r) = v in node l (f b) r


------------------------------------------------------------------------
-- Correct-by-construction functions working on buffer-bound data

namespace Pointer


  orM : Singleton b -> IO (Singleton c) -> IO (Singleton (b || c))
  orM (MkSingleton True) _ = pure [| True |]
  orM (MkSingleton False) io = io

  ||| Find a byte
  export
  find : (tgt : Bits8) -> Pointer.Mu Tree t -> IO (Singleton (find tgt t))
  find tgt ptr = case !(view ptr) of
    "Leaf" # _ => pure [| False |]
    "Node" # l # b # r => ((== tgt) <$> b)
      `orM` do !(find tgt l) `orM` find tgt r

  ||| Correct by construction sum function.
  ||| @ t   is the phantom name of the tree represented by the buffer
  ||| @ ptr is the position of t inside the buffer
  ||| Singleton ensures that the value we return is the same as if
  ||| we had directly processed `t`.
  export
  sum : (ptr : Pointer.Mu Tree t) ->
        IO (Singleton (Data.sum t))
  sum ptr = case !(view ptr) of
    "Leaf" # t => pure (MkSingleton 0)
    "Node" # l # b # r =>
      do m <- sum l
         n <- sum r
         pure [| [| m + [| cast b |] |] + n |]

  export
  leftBranch : Pointer.Mu Tree t -> IO (Pointer.Mu Tree (Data.leftBranch t))
  leftBranch ptr = case !(view ptr) of
    "Leaf" # _ => pure ptr
    "Node" # l # b # r => pure l

  export
  rightBranch : Pointer.Mu Tree t -> IO (Pointer.Mu Tree (Data.rightBranch t))
  rightBranch ptr = case !(view ptr) of
    "Leaf" # _ => pure ptr
    "Node" # l # b # r => pure r

  export
  rightmost : Pointer.Mu Tree t -> IO (Singleton (rightmost t))
  rightmost t = case !(view t) of
    "Leaf" # el => pure [| Nothing |]
    "Node" # _ # b # r => map ((Just <$>) . (fromMaybe . delay <$> b <*>)) (rightmost r)

  export
  swap : Pointer.Mu Tree t -> Serialising Tree (Data.swap t)
  swap ptr = case !(view ptr) of
    "Leaf" # () => "Leaf" # ()
    "Node" # l # b # r => "Node" # copy r # b # copy l

  export
  ||| This is an inefficient version using `deepCopy`
  deepSwap : Pointer.Mu Tree t -> Serialising Tree (Data.swap t)
  deepSwap ptr = case !(view ptr) of
    "Leaf" # () => "Leaf" # ()
    "Node" # l # b # r => "Node" # deepCopy r # b # deepCopy l

  ||| Correct by construction map function.
  ||| @ f   is the function to map over the tree's nodes
  ||| @ t   is the phantom name of the tree represented by the buffer
  ||| @ ptr is the position of t inside the buffer
  ||| Serialising ensures that the value we compute is the same as if
  ||| we had directly processed `t`.
  export
  map : (f : Bits8 -> Bits8) ->
        (ptr : Pointer.Mu Tree t) ->
        Serialising Tree (Data.map f t)
  map f ptr = case !(view ptr) of
    "Leaf" # () => "Leaf" # ()
    "Node" # l # b # r => "Node" # map f l # (f <$> b) # map f r

  ||| Simple printing function
  export
  display : Pointer.Mu Tree t -> IO String
  display ptr = case !(out ptr) of
    "Leaf" # t => pure "leaf"
    "Node" # t => do
      (l # b # r) <- layer t
      l <- display l
      r <- display r
      pure "(node \{l} \{show (getSingleton b)} \{r})"
