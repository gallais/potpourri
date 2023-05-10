module Serialised.Desc

import Control.Monad.State

import Data.Buffer
import Data.Fin
import Data.String
import Data.Vect

import Decidable.Equality

import Lib

%default total

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

||| A description is a nested tuple of Bytes or recursive positions
||| It is indexed by 1 'input' parameter and 2 'ouput' indices:
|||  @rightmost telling us whether we are in the rightmost subterm
|||             in which case `Rec` won't need to record an additional offset
|||  @static    the statically known part of the size (in number of bytes)
|||  @offsets   the dynamically known part of the size (in number of subtrees)
public export
data Desc : (rightmost : Bool) -> (static : Nat) -> (offsets : Nat) -> Type where
  None : Desc r 0 0
  Byte : Desc r 1 0
  Prod : {sl, sr, m, n : Nat} -> -- does not matter: Descs are meant to go away with staging
         (d : Desc False sl m) ->
         (e : Desc r sr n) ->
         Desc r (sl + sr) (m + n)
  Rec : Desc r 0 (ifThenElse r 0 1)

||| A constructor description is essentially an existential type
||| around a description
||| @ nm is the type of name we use for the constructor
public export
record Constructor (nm : Type) where
  constructor (::)
  name : nm
  {static : Nat}
  {offsets : Nat}
  description : Desc True static offsets

||| A data description is a sum over a list of constructor types
public export
record Data (nm : Type) where
  constructor MkData
  {consNumber : Nat}
  constructors : Vect consNumber (Constructor nm)

||| A wrapper around fin that helps unification
public export
record Index (cs : Data nm) where
  constructor MkIndex
  getIndex : Fin (consNumber cs)

||| A smart projection
public export
description : {cs : Data nm} -> (k : Index cs) ->
              let cons = index (getIndex k) (constructors cs) in
              Desc True (static cons) (offsets cons)
description {cs} k = description (index (getIndex k) (constructors cs))

||| A little bit of magic
public export
fromString : {cs : Data String} -> (str : String) ->
             {auto 0 _ : IsJust (findIndex ((str ==) . Constructor.name) (constructors cs))} ->
             Index cs
fromString {cs} str with (findIndex ((str ==) . Constructor.name) (constructors cs))
  _ | Just k = MkIndex k

||| Another kind of magic
public export
fromInteger : {cs : Data nm} -> (k : Integer) ->
              {auto 0 _ : So (consNumber cs /= 0)} ->
              Index cs
fromInteger {cs = MkData (_::_)} k = MkIndex (restrict _ k)

export
DecEq (Index cs) where
  decEq (MkIndex k) (MkIndex l) with (decEq k l)
    decEq (MkIndex k) (MkIndex .(k)) | Yes Refl = Yes Refl
    decEq (MkIndex k) (MkIndex l) | No notEq = No (notEq . cong getIndex)

------------------------------------------------------------------------
-- Show instances

export
Show (Desc r s o) where
  showPrec _ None = "()"
  showPrec _ Byte = "Bits8"
  showPrec p (Prod d e) =
    showParens (p <= Open) $ showPrec Open d ++ " * " ++ showPrec App e
  showPrec _ Rec = "X"

export
Show (Data nm) where
  show cs = go (constructors cs) where

    go : Vect n (Constructor _) -> String
    go [] = "⊥"
    go (c :: cs) = concat
      $  ("μX. " ++ show (description c))
      :: ((" + " ++) <$> map (\ c => show (description c)) cs)

------------------------------------------------------------------------
-- Eq instances

||| Heterogeneous equality check for descriptions
eqDesc : Desc r s o -> Desc r' s' n' -> Bool
eqDesc None None = True
eqDesc Byte Byte = True
eqDesc (Prod d e) (Prod s t) = eqDesc d s && eqDesc e t
eqDesc Rec Rec = True
eqDesc _ _ = False

export
eqConstructor : Constructor a -> Constructor b -> Bool
eqConstructor (_ :: d) (_ :: e) = eqDesc d e

||| Heterogeneous equality check for vectors of constructors
eqConstructors : Vect m (Constructor a) -> Vect n (Constructor b) -> Bool
eqConstructors [] [] = True
eqConstructors (c :: cs) (c' :: cs') = eqConstructor c c' && eqConstructors cs cs'
eqConstructors _ _ = False

export
eqData : Data a -> Data b -> Bool
eqData (MkData cs) (MkData cs') = eqConstructors cs cs'

------------------------------------------------------------------------
-- Serialisation of descriptions to a Buffer

parameters (buf : Buffer)

  ||| Set a description in a buffer
  ||| @ start position in the buffer to set the description at
  ||| @ d     description to serialise
  ||| Returns the end position
  setDesc : (start : Int) -> (d : Desc r s o) -> IO Int
  setDesc start None = (start + 1) <$ setBits8 buf start 0
  setDesc start Byte = (start + 1) <$ setBits8 buf start 1
  setDesc start (Prod d e)
    = do setBits8 buf start 2
         afterLeft <- setDesc (start + 1) d
         setDesc afterLeft e
  setDesc start Rec = (start + 1) <$ setBits8 buf start 3

  ||| Set a list of constructors one after the other in a buffer
  ||| @ start position in the buffer to set the constructors at
  ||| @ cs    list of constructors to serialise
  ||| Returns the end position
  setConstructors : (start : Int) -> (cs : Vect n (Constructor _)) -> IO Int
  setConstructors start [] = pure start
  setConstructors start ((_ :: d) :: cs)
    = do afterC <- setDesc start d
         setConstructors afterC cs

  ||| Set data description in a buffer
  ||| @ start position in the buffer to set the data description at
  ||| @ cs    data description to serialise
  ||| Returns the end position
  export
  setData : (start : Int) -> (cs : Data nm) -> IO Int
  setData start (MkData {consNumber} cs) = do
    -- We first store the length of the list so that we know how
    -- many constructors to deserialise on the way out
    setBits8 buf start (cast consNumber)
    setConstructors (start + 1) cs

  ||| Existential wrapper to deserialise descriptions
  ||| @ rightmost is known statically but the others indices are not
  record IDesc (rightmost : Bool) where
    constructor MkIDesc
    {static : Nat}
    {offsets : Nat}
    runIDesc : Desc rightmost static offsets

  ||| Auxiliary definition to help idris figure out the types of
  ||| everything involved
  IProd : IDesc False -> IDesc r -> IDesc r
  IProd (MkIDesc d) (MkIDesc e) = MkIDesc (Prod d e)

  ||| Get a description from a buffer
  ||| @ start position the description starts at in the buffer
  ||| Returns the end position & the description
  getDesc : {r : Bool} -> Int -> IO (Int, IDesc r)
  getDesc start = case !(getBits8 buf start) of
    0 => pure (start + 1, MkIDesc None)
    1 => pure (start + 1, MkIDesc Byte)
    2 => do (afterLeft, d) <- assert_total (getDesc {r = False} (start + 1))
            (end, e) <- assert_total (getDesc {r} afterLeft)
            pure (end, IProd d e)
    3 => pure (start + 1, MkIDesc Rec)
    _ => failWith "Invalid Description"

  ||| Get a list of constructor from a buffer
  ||| @ start position the list of constructors starts at in the buffer
  ||| @ n     number of constructors to deserialise
  getConstructors : (start : Int) -> (n : Nat) -> IO (Vect n (Constructor ()))
  getConstructors start 0 = pure []
  getConstructors start (S n)
    = do (afterD, d) <- getDesc start
         cs <- getConstructors afterD n
         pure ((() :: runIDesc d) :: cs)

  ||| Get a data description from a buffer
  ||| @ start position the data description starts at in the buffer
  export
  getData : Int -> IO (Data ())
  getData start = do
    n <- getBits8 buf start
    let Just n = ifThenElse (n < 0) Nothing (Just (cast n))
       | Nothing => failWith "Invalid header"
    MkData <$> getConstructors (start + 1) n


------------------------------------------------------------------------
-- Meaning of descriptions as functors

namespace Data

  ||| Meaning where subterms are interpreted using the parameter
  public export
  Meaning : Desc r s o -> Type -> Type
  Meaning None x = ()
  Meaning Byte x = Bits8
  Meaning (Prod d e) x = (Meaning d x * Meaning e x)
  Meaning Rec x = x

  public export
  Meaning' : Desc r s o -> Type -> Type -> Type
  Meaning' None x r = r
  Meaning' Byte x r = Bits8 -> r
  Meaning' (Prod d e) x r = Meaning' d x (Meaning' e x r)
  Meaning' Rec x r = x -> r

  public export
  curry : (d : Desc r s o) -> (Meaning d x -> a) -> Meaning' d x a
  curry None k = k ()
  curry Byte k = k
  curry (Prod d e) k = curry d (curry e . curry k)
  curry Rec k = k

  public export
  fmap : (d : Desc{}) -> (a -> b) -> Meaning d a -> Meaning d b
  fmap None f v = v
  fmap Byte f v = v
  fmap (Prod d e) f (v # w) = (fmap d f v # fmap e f w)
  fmap Rec f v = f v

  export
  fmapId : (d : Desc{}) -> (f : a -> a) -> ((x : a) -> f x === x) ->
           (t : Meaning d a) -> fmap d f t === t
  fmapId None f eq t = Refl
  fmapId Byte f eq t = Refl
  fmapId (Prod d e) f eq (t # u) = cong2 (#) (fmapId d f eq t) (fmapId e f eq u)
  fmapId Rec f eq t = eq t

  public export
  traverse : Monad m => (d : Desc{}) ->
             (a -> m b) -> Meaning d a -> m (Meaning d b)
  traverse None f v = pure v
  traverse Byte f v = pure v
  traverse (Prod d e) f (v # w) = [| traverse d f v # traverse e f w |]
  traverse Rec f v = f v

------------------------------------------------------------------------
-- Meaning of data descriptions as fixpoints

  public export
  Alg : Data nm -> Type -> Type
  Alg cs x = (k : Index cs) -> Meaning (description k) x -> x

  ||| Fixpoint of the description:
  ||| 1. pick a constructor
  ||| 2. give its meaning where subterms are entire subtrees
  public export
  data Mu : Data nm -> Type where
    (#) : Alg cs (assert_total (Mu cs))

  ||| Curried version of the constructor; more convenient to use
  ||| when writing examples
  public export
  mkMu : (cs : Data nm) -> (k : Index cs) ->
         Meaning' (description k) (Mu cs) (Mu cs)
  mkMu cs k = curry (description k) (Data.(#) k)

  ||| Fixpoints are initial algebras
  public export
  fold : {cs : Data nm} -> Alg cs a -> Mu cs -> a
  fold alg (k # t) = alg k (assert_total $ fmap _ (fold alg) t)

------------------------------------------------------------------------
-- Examples

namespace Tree

  public export
  Tree : Data String
  Tree = MkData
    [ "Leaf" :: None
    , "Node" :: Prod Rec (Prod Byte Rec)
    ]

  public export
  ATree : Type
  ATree = Data.Mu Tree

  public export
  leaf : ATree
  leaf = mkMu Tree "Leaf"

  public export
  node : ATree -> Bits8 -> ATree -> ATree
  node = mkMu Tree "Node"

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
