module Free.Common

%default total

public export
Pred : Type -> Type
Pred a = a -> Type

public export
Rel : Type -> Type
Rel a = a -> a -> Type

infixr 5 :>
public export
data Fwd : Rel a -> Rel a where
  FNil : Fwd r i i
  (:>) : {0 r : Rel a} -> r i j -> Fwd r j k -> Fwd r i k

namespace Fwd

  export
  (++) : Fwd m i j -> Fwd m j k -> Fwd m i k
  FNil      ++ ys = ys
  (x :> xs) ++ ys = x :> (xs ++ ys)

namespace Fwd1

  public export
  data Fwd1 : Rel a -> Rel a where
    (:>) : {0 r : Rel a} -> r i j -> Fwd r j k -> Fwd1 r i k

  export
  forget : Fwd1 m i j -> Fwd m i j
  forget (x :> xs) = x :> xs

  export
  (++) : Fwd1 m i j -> Fwd1 m j k -> Fwd1 m i k
  (x :> xs) ++ ys = x :> (xs ++ forget ys)

infixl 5 :<
public export
data Bwd : Rel a -> Rel a where
  BNil : Bwd r i i
  (:<) : {0 r : Rel a} -> Bwd r i j -> r j k -> Bwd r i k

infixl 3 <><
export
(<><) : Bwd r i j -> Fwd r j k -> Bwd r i k
fs <>< FNil = fs
fs <>< (g :> gs) = (fs :< g) <>< gs
infixr 3 <>>

namespace Fwd1

  export
  (<>>) : Bwd m i j -> Fwd1 m j k -> Fwd1 m i k
  BNil <>> ys = ys
  (xs :< x) <>> ys = xs <>> (x :> forget ys)

namespace Bwd1

  public export
  data Bwd1 : Rel a -> Rel a where
    (:<) : {0 r : Rel a} -> Bwd r i j -> r j k -> Bwd1 r i k

  export
  forget : Bwd1 m i j -> Bwd m i j
  forget (xs :< x) = xs :< x

  export
  (<><) : Bwd1 m i j -> Fwd m j k -> Bwd1 m i k
  xs <>< FNil = xs
  xs <>< (y :> ys) = (forget xs :< y) <>< ys

  export
  reverse : Bwd1 m i j -> Fwd1 m i j
  reverse (xs :< x) = xs <>> (x :> FNil)

namespace Fwd1

  export
  reverse : Fwd1 m i j -> Bwd1 m i j
  reverse (x :> xs) = (BNil :< x) <>< xs

  export
  concat : Bwd1 (Fwd1 m) i j -> Fwd1 m i j
  concat (fss :< fs) = go fss fs where

    go : Bwd (Fwd1 m) x y -> Fwd1 m y z -> Fwd1 m x z
    go BNil acc = acc
    go (fss :< fs) acc = go fss (fs ++ acc)

namespace Fwd

  export
  reverse : Fwd r i j -> Bwd r i j
  reverse = (BNil <><)

export
(<>>) : Bwd r i j -> Fwd r j k -> Fwd r i k
BNil <>> gs = gs
(fs :< f) <>> gs = fs <>> (f :> gs)

namespace Bwd

  export
  reverse : Bwd r i j -> Fwd r i j
  reverse = (<>> FNil)

public export
Kleisli : Pred Type -> Rel Type
Kleisli m a b = a -> m b
