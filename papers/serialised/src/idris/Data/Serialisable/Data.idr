module Data.Serialisable.Data

import Data.Singleton

import Lib
import Data.Serialisable.Desc

------------------------------------------------------------------------
-- Meaning of descriptions as functors

||| Meaning where subterms are interpreted using the parameter
public export
Meaning : Desc r s o -> Type -> Type
Meaning None x = ()
Meaning Byte x = Bits8
Meaning (Prod d e) x = (Meaning d x * Meaning e x)
Meaning Rec x = x

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

export
fmapCompose :
  (d : Desc{}) -> (g : b -> c) -> (f : a -> b) -> (gf : a -> c) ->
  ((x : a) -> g (f x) === gf x) ->
  (t : Meaning d a) -> fmap d g (fmap d f t) === fmap d gf t
fmapCompose None g f gf eq t = Refl
fmapCompose Byte g f gf eq t = Refl
fmapCompose (Prod d e) g f gf eq (t # u)
  = cong2 (#) (fmapCompose d g f gf eq t) (fmapCompose e g f gf eq u)
fmapCompose Rec g f gf eq t = eq t

public export
traverse : Monad m => (d : Desc{}) ->
           (a -> m b) -> Meaning d a -> m (Meaning d b)
traverse None f v = pure v
traverse Byte f v = pure v
traverse (Prod d e) f (v # w) = [| traverse d f v # traverse e f w |]
traverse Rec f v = f v

namespace All

  data All' : (d : Desc r s o) -> (p : x -> Type) -> Meaning d x -> Type

  public export
  All : (d : Desc r s o) -> (p : x -> Type) -> Meaning d x -> Type
  All None p t = ()
  All Byte p t = Singleton t
  All d@(Prod _ _) p t = All' d p t
  All Rec p t = p t

  public export
  data All' : (d : Desc r s o) -> (p : x -> Type) -> Meaning d x -> Type where
    (#) : All d p t -> All e p u -> All' (Prod d e) p (t # u)

  export
  all : (d : Desc r s o) -> ((a : x) -> p a) ->
        (t : Meaning d x) -> All d p t
  all None f t = t
  all Byte f t = MkSingleton t
  all (Prod d e) f (t # u) = (all d f t # all e f u)
  all Rec f t = f t

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

||| Fixpoints are initial algebras
public export
fold : {cs : Data nm} -> Alg cs a -> Mu cs -> a
fold alg (k # t) = alg k (assert_total $ fmap _ (fold alg) t)
