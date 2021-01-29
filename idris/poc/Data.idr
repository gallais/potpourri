module Data

import Data.Stream

%default total

namespace Data

  public export
  interface Data t where

    0 Base' : Type -> Type
    functor : Functor Base'

    wrap : Base' t -> t
    unwrap : t -> Base' t

    cata : (Base' a -> a) -> t -> a

    para : (Base' (a, t) -> a) -> t -> a
    para alg = fst . cata (\ ih => (alg ih, wrap (map @{functor} snd ih)))

  public export
  0 Base : (0 t : Type) -> Data t => Type -> Type
  Base t @{d} = Base' @{d}

  public export
  data Mu : (Type -> Type) -> Type where
    MkMu : f (Mu f) -> Mu f

  public export
  partial
  fold : Functor f => (f a -> a) -> Mu f -> a
  fold alg (MkMu p) = alg (map (fold alg) p)

  partial
  toMu : Data t => t -> Mu (Base t)
  toMu = cata MkMu

  partial
  fromMu : Data t => Mu (Base t) -> t
  fromMu = fold @{functor} wrap


[FUNCTOR] {arg : {0 a, b : Type} -> (a -> b) -> f a -> f b} -> Functor f where map = arg

namespace List

  public export
  uncons : List a -> Maybe (a, List a)
  uncons [] = Nothing
  uncons (x :: xs) = Just (x, xs)

  public export
  cons : Maybe (a, List a) -> List a
  cons = maybe Nil (uncurry (::))

Data (List a) where

  Base' = Maybe . (a,)
  functor = FUNCTOR {arg = map . map}

  wrap = cons
  unwrap = uncons

  cata alg = foldr (curry (alg . Just)) (alg Nothing)

namespace Colist

  public export
  data Colist : Type -> Type where
    Nil : Colist a
    (::) : a -> Inf (Colist a) -> Colist a

  public export
  cons : Maybe (a, Inf (Colist a)) -> Colist a
  cons = maybe Nil (uncurry (::))

  public export
  uncons : Colist a -> Maybe (a, Inf (Colist a))
  uncons [] = Nothing
  uncons (x :: xs) = Just (x, xs)

  public export
  unfold : (s -> Maybe (a, s)) -> s -> Colist a
  unfold next seed = case next seed of
    Nothing => []
    Just (a, seed) => a :: unfold next seed

  public export
  take : Nat -> Colist a -> List a
  take Z _ = []
  take _ [] = []
  take (S k) (x :: xs) = x :: take k xs

inf : a -> Inf a
inf x = x

fni : Inf a -> a
fni x = x

namespace Codata

  public export
  interface Codata t where

    0 Cobase' : Type -> Type
    functor : Functor Cobase'

    wrap : Cobase' (Inf t) -> t
    unwrap : t -> Cobase' (Inf t)

    ana : (s -> Cobase' s) -> s -> t

  public export
  0 Cobase : (0 t : Type) -> Codata t => Type -> Type
  Cobase t @{d} = Cobase' @{d}

  public export
  data Nu : (Type -> Type) -> Type where
    MkNu : {0 f : Type -> Type} -> f (Inf (Nu f)) -> Nu f

  public export
  partial
  unfold : Functor f => (s -> f s) -> s -> Nu f
  unfold coalg seed = MkNu $ (map (inf . unfold coalg) (coalg seed))

  partial
  toNu : Codata t => t -> Nu (Cobase t)
  toNu = unfold @{Codata.functor} (map @{Codata.functor} fni . Codata.unwrap)

  partial
  fromNu : Codata t => Nu (Cobase t) -> t
  fromNu = ana ?b

Codata (Colist a) where

  Cobase' = Maybe . (a,)
  functor = FUNCTOR {arg = map . map}

  wrap = cons
  unwrap = uncons

  ana = unfold

Codata (Stream a) where

  Cobase' = (a,)
  functor = FUNCTOR {arg = map}

  wrap = uncurry (::)
  unwrap = \ (x :: xs) => (x, xs)

  ana = unfoldr

fromData : (Data d, Codata c) => ({0 a : Type} -> Base d a -> Cobase c a) -> d -> c
fromData f = cata (Codata.wrap . f . map @{Data.functor} inf)

fromCodata : (Codata c1, Codata c2) => ({0 a : Type} -> Cobase c1 a -> Cobase c2 a) -> c1 -> c2
fromCodata f = ana (map @{Codata.functor} fni . f . Codata.unwrap)

fromList : List a -> Colist a
fromList = fromData id

fromStream : Stream a -> Colist a
fromStream = fromCodata Just
