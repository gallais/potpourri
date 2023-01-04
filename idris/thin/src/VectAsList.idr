module VectAsList

%default total

export
record Vect (n : Nat) (a : Type) where
  constructor MkVect
  encoding : List a
  0 valid : length encoding === n

namespace Smart

  public export
  Nil : Vect Z a
  Nil = MkVect [] Refl

  public export
  (::) : a -> Vect n a -> Vect (S n) a
  x :: MkVect xs eq = MkVect (x :: xs) (cong S eq)

public export
data View : Vect n a -> Type where
  Nil : View Nil
  (::) : (x : a) -> (xs : Vect n a) -> View (x :: xs)

namespace Smart

  public export
  view : (xs : Vect n a) -> View xs
  view (MkVect [] Refl) = Nil
  view (MkVect (x :: xs) Refl) = x :: MkVect xs Refl

export
map : (a -> b) -> Vect n a -> Vect n b
map f xs@_ with (view xs)
  _ | [] = []
  _ | hd :: tl = f hd :: map f tl

(++) : Vect m a -> Vect n a -> Vect (m + n) a
xs@_ ++ ys with (view xs)
  _ | [] = ys
  _ | hd :: tl = hd :: (tl ++ ys)

data SplitAt : (m : Nat) -> (xs : Vect p a) -> Type where
  MkSplitAt : (pref : Vect m a) -> (suff : Vect n a) ->
              SplitAt m (pref ++ suff)

namespace SplitAt

 export
 (::) : (x : a) -> SplitAt m xs -> SplitAt (S m) (x :: xs)
 x :: MkSplitAt pref@(MkVect _ Refl) suff
   = MkSplitAt (x :: pref) suff

failing "tl is not accessible in this context"

  splitAt : (m : Nat) -> (xs : Vect (m + n) a) -> SplitAt m xs
  splitAt 0 xs = MkSplitAt [] xs
  splitAt (S m) xs@_ with (view xs)
    _ | hd :: tl@_ with (splitAt m tl)
      _ | res = ?a

failing "Can't match on ?postpone [no locals in scope] (User dotted)"

  splitAt : (m : Nat) -> (xs : Vect (m + n) a) -> SplitAt m xs
  splitAt 0 xs = MkSplitAt [] xs
  splitAt (S m) xs@_ with (view xs)
    _ | hd :: tl with (splitAt m tl)
      splitAt (S m) .(hd :: (pref ++ suff))
        | hd :: .(pref ++ suff)
        | MkSplitAt pref suff = ?a

splitAt : (m : Nat) -> (xs : Vect (m + n) a) -> SplitAt m xs
splitAt 0 xs = MkSplitAt [] xs
splitAt (S m) xs@_ with (view xs)
  _ | hd :: tl = hd :: splitAt m tl
