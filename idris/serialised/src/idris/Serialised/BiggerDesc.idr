module Serialised.BiggerDesc

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

||| A base type is indexed by two 'output' indices:
|||  @size      the statically known part of the size (in number of bytes)
|||  @offsets   the dynamically known part of the size (in number of boxes)
public export
data Base : (size : Nat) -> (offsets : Nat) -> Type where
  AUnit : Base 0 0
  -- numeric type, known size
  ABits8 : Base 1 0
  AnInt8 : Base 1 0
  ABits16 : Base 2 0
  AnInt16 : Base 2 0
  ABits32 : Base 4 0
  AnInt32 : Base 4 0
  ABits64 : Base 8 0
  AnInt64 : Base 8 0
  -- Boxed types
  AnInteger : Base 0 1
  ANat : Base 0 1
  AString : Base 0 1

namespace Base

  export
  index : Base s n -> Bits8
  index AUnit = 0
  index ABits8 = 1
  index AnInt8 = 2
  index ABits16 = 3
  index AnInt16 = 4
  index ABits32 = 5
  index AnInt32 = 6
  index ABits64 = 7
  index AnInt64 = 8
  index AnInteger = 9
  index ANat = 10
  index AString = 11

  record IBase where
    constructor MkIBase
    {size : Nat}
    {offsets : Nat}
    runIBase : Base size offsets

  export
  unindex : (tag : Bits8) -> Maybe (ib : IBase ** index (runIBase ib) === tag)
  unindex 0 = Just (MkIBase AUnit ** Refl)
  unindex 1 = Just (MkIBase ABits8 ** Refl)
  unindex 2 = Just (MkIBase AnInt8 ** Refl)
  unindex 3 = Just (MkIBase ABits16 ** Refl)
  unindex 4 = Just (MkIBase AnInt16 ** Refl)
  unindex 5 = Just (MkIBase ABits32 ** Refl)
  unindex 6 = Just (MkIBase AnInt32 ** Refl)
  unindex 7 = Just (MkIBase ABits64 ** Refl)
  unindex 8 = Just (MkIBase AnInt64 ** Refl)
  unindex 9 = Just (MkIBase AnInteger ** Refl)
  unindex 10 = Just (MkIBase ANat ** Refl)
  unindex 11 = Just (MkIBase AString ** Refl)
  unindex tag = Nothing

  public export
  Meaning : Base s n -> Type
  Meaning AUnit = ()
  Meaning ABits8 = Bits8
  Meaning AnInt8 = Int8
  Meaning ABits16 = Bits16
  Meaning AnInt16 = Int16
  Meaning ABits32 = Bits32
  Meaning AnInt32 = Int32
  Meaning ABits64 = Bits64
  Meaning AnInt64 = Int64
  Meaning AnInteger = Integer
  Meaning ANat = Nat
  Meaning AString = String

||| A description is a nested tuple of Bytes or recursive positions
||| It is indexed by 1 'input' parameter and 2 'ouput' indices:
|||  @rightmost telling us whether we are in the rightmost subterm
|||             in which case `Rec` won't need to record an additional offset
|||  @size      the statically known part of the size (in number of bytes)
|||  @offsets   the dynamically known part of the size (in number of subtrees)
public export
data Desc : (rightmost : Bool) -> (size : Nat) -> (offsets : Nat) -> Type where
  Val : Base s n -> Desc r s n
  Prd : {sl, sr, m, n : Nat} -> -- does not matter: Descs are meant to go away with staging
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
  {size : Nat}
  {offsets : Nat}
  description : Desc True size offsets

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
              Desc True (size cons) (offsets cons)
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
Show (Base s n) where
  show AUnit = "()"
  show ABits8 = "Bits8"
  show AnInt8 = "Int8"
  show ABits16 = "Bits16"
  show AnInt16 = "Int16"
  show ABits32 = "Bits32"
  show AnInt32 = "Int32"
  show ABits64 = "Bits64"
  show AnInt64 = "Int64"
  show AnInteger = "Integer"
  show ANat = "Nat"
  show AString = "String"

export
Show (Desc r s n) where
  showPrec _ (Val b) = show b
  showPrec p (Prd d e) =
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

||| Heterogenous equality check for base types
eqBase : Base s n -> Base s' n' -> Bool
eqBase AUnit AUnit = True
eqBase ABits8 ABits8 = True
eqBase AnInt8 AnInt8 = True
eqBase ABits16 ABits16 = True
eqBase AnInt16 AnInt16 = True
eqBase ABits32 ABits32 = True
eqBase AnInt32 AnInt32 = True
eqBase ABits64 ABits64 = True
eqBase AnInt64 AnInt64 = True
eqBase AnInteger AnInteger = True
eqBase ANat ANat = True
eqBase AString AString = True
eqBase _ _ = False

||| Heterogeneous equality check for descriptions
eqDesc : Desc r s n -> Desc r' s' n' -> Bool
eqDesc (Val d) (Val e) = eqBase d e
eqDesc (Prd d e) (Prd s t) = eqDesc d s && eqDesc e t
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
  setDesc : (start : Int) -> (d : Desc r s n) -> IO Int
  setDesc start (Prd d e)
    = do setBits8 buf start 0
         afterLeft <- setDesc (start + 1) d
         setDesc afterLeft e
  setDesc start Rec = (start + 1) <$ setBits8 buf start 1
  setDesc start (Val d) = (start + 1) <$ setBits8 buf start (2 + Base.index d)

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
    {size : Nat}
    {offsets : Nat}
    runIDesc : Desc rightmost size offsets

  ||| Auxiliary definition to help idris figure out the types of
  ||| everything involved
  IPrd : IDesc False -> IDesc r -> IDesc r
  IPrd (MkIDesc d) (MkIDesc e) = MkIDesc (Prd d e)

  ||| Get a description from a buffer
  ||| @ start position the description starts at in the buffer
  ||| Returns the end position & the description
  getDesc : {r : Bool} -> Int -> IO (Int, IDesc r)
  getDesc start = case !(getBits8 buf start) of
    0 => do (afterLeft, d) <- assert_total (getDesc {r = False} (start + 1))
            (end, e) <- assert_total (getDesc {r} afterLeft)
            pure (end, IPrd d e)
    1 => pure (start + 1, MkIDesc Rec)
    n => case unindex (n-2) of
      Just (MkIBase d ** _) => pure (start + 1, MkIDesc (Val d))
      Nothing => failWith "Invalid Description"

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
  Meaning : Desc r s n -> Type -> Type
  Meaning (Val d) x = Base.Meaning d
  Meaning (Prd d e) x = (Meaning d x * Meaning e x)
  Meaning Rec x = x

  public export
  Meaning' : Desc r s n -> Type -> Type -> Type
  Meaning' (Val d) x r = Base.Meaning d -> r
  Meaning' (Prd d e) x r = Meaning' d x (Meaning' e x r)
  Meaning' Rec x r = x -> r

  public export
  curry : (d : Desc r s n) -> (Meaning d x -> a) -> Meaning' d x a
  curry (Val d) k = k
  curry (Prd d e) k = curry d (curry e . curry k)
  curry Rec k = k

  public export
  fmap : {d : Desc{}} -> (a -> b) -> Meaning d a -> Meaning d b
  fmap {d = Val d} f v = v
  fmap {d = Prd d e} f (v # w) = (fmap f v # fmap f w)
  fmap {d = Rec} f v = f v

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
  fold : {cs : Data nm} -> (alg : Alg cs a) -> (t : Mu cs) -> a
  fold alg (k # t) = alg k (assert_total $ fmap (fold alg) t)

------------------------------------------------------------------------
-- Examples

namespace Tree

  public export
  Tree : Data String
  Tree = MkData
    [ "Leaf" :: Prd (Val AnInteger) (Prd (Val AString) (Val ANat))
    , "Node" :: Prd Rec (Prd (Val ABits16) Rec)
    ]

  public export
  ATree : Type
  ATree = Data.Mu Tree

  public export
  leaf : Integer -> String -> Nat -> ATree
  leaf = mkMu Tree "Leaf"

  public export
  node : ATree -> Bits16 -> ATree -> ATree
  node = mkMu Tree "Node"

  public export
  example : ATree
  example =
    (node
      (node (node (leaf (-10) "h" 10) 1 (leaf (-6) "e" 6))
            5
            (leaf (-1) "l" 1))
      10
      (node (leaf (-2) "l" 2) 20 (leaf (-9) "o world!" 9)))
