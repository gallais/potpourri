module VectAsList

import FinAsNat

%default total

||| A vector of as of size n is defined as
||| 1. its encoding as a list of as
||| 2. a runtime irrelevant proof that the encoding's length is n
|||
||| This replace the usual definition as an inductive family:
|||
|||   data Vect : Nat -> Type -> Type where
|||     Nil : Vect 0 a
|||     (::) : a -> Vect n a -> Vect (S n) a
export
record Vect (n : Nat) (a : Type) where
  constructor MkVect
  encoding : List a
  0 valid : length encoding === n

||| We can recover the usual Nil, (::) interface by defining smart constructors
namespace Smart

  ||| The constructor for the empty vector
  public export
  Nil : Vect Z a
  Nil = MkVect [] Refl

  ||| The constructor combinding a head and a tail of size n
  ||| to obtain a vector of size (S n)
  public export
  (::) : a -> Vect n a -> Vect (S n) a
  x :: MkVect xs eq = MkVect (x :: xs) (cong S eq)

||| In order to pattern-match on such vectors, we need to define a view.
||| Pattern-matching on a value of type (View xs) will reveal whether
||| xs was built using Nil, or by combining a head and a tail using (::).
public export
data View : Vect n a -> Type where
  Nil : View Nil
  (::) : (x : a) -> (xs : Vect n a) -> View (x :: xs)

namespace Smart

  ||| Prove that for any vector, we can compute a view associated to it
  ||| i.e. all vectors are either Nil or (::)-headed.
  public export
  view : (xs : Vect n a) -> View xs
  view (MkVect [] Refl) = Nil
  view (MkVect (x :: xs) Refl) = x :: MkVect xs Refl

||| (Vect n) is a functor. This definition demonstrates how we can use
||| the view on the LHS to 'pattern-match' on vectors and smart constructors
||| on the RHS to build new ones.
export
map : (a -> b) -> Vect n a -> Vect n b
map f xs@_ with (view xs)
  _ | [] = []
  _ | hd :: tl = f hd :: map f tl

||| Using the Fin type defined in FinAsNat, we can define a lookup
||| function which, at runtime, will be exactly like its partial
||| counterpart of type `List a -> Nat -> a`.
lookup : Vect n a -> Fin n -> a
lookup xs@_ k@_ with (view xs) | (view k)
  _ | hd :: _ | Z = hd
  _ | _ :: tl | S k' = lookup tl k'

||| Appending to vectors of respective sizes m and n,
||| yields a new vector of size (m + n).
(++) : Vect m a -> Vect n a -> Vect (m + n) a
xs@_ ++ ys with (view xs)
  _ | [] = ys
  _ | hd :: tl = hd :: (tl ++ ys)

||| (SplitAt m) is a view stating that a given vector xs was built
||| by appending a prefix of size m in front of a suffix.
||| It is named by analogy with the classic Haskell function
||| splitAt :: Int -> [a] -> ([a], [a])
data SplitAt : (m : Nat) -> (xs : Vect p a) -> Type where
  MkSplitAt : (pref : Vect m a) -> (suff : Vect n a) ->
              SplitAt m (pref ++ suff)

namespace SplitAt

 ||| If we know how to split a vector xs at index m, then we know
 ||| how to split (x :: xs) at index (S m): we can simply push x
 ||| on top of the prefix.
 export
 (::) : (x : a) -> SplitAt m xs -> SplitAt (S m) (x :: xs)
 x :: MkSplitAt pref@(MkVect _ Refl) suff
   = MkSplitAt (x :: pref) suff

-- Now the failing attempts to define splitAt as per appendix B:

-- Bug in Idris 2: In (tl@_), tl is arbitrarily assigned quantity 0
-- which then prevents us from calling (splitAt m tl)
failing "tl is not accessible in this context"

  splitAt : (m : Nat) -> (xs : Vect (m + n) a) -> SplitAt m xs
  splitAt 0 xs = MkSplitAt [] xs
  splitAt (S m) xs@_ with (view xs)
    _ | hd :: tl@_ with (splitAt m tl)
      _ | res = ?a

-- Bug in Idris 2: case-splitter attempts to split on a forced pattern
failing "Can't match on ?postpone [no locals in scope] (User dotted)"

  splitAt : (m : Nat) -> (xs : Vect (m + n) a) -> SplitAt m xs
  splitAt 0 xs = MkSplitAt [] xs
  splitAt (S m) xs@_ with (view xs)
    _ | hd :: tl with (splitAt m tl)
      splitAt (S m) .(hd :: (pref ++ suff))
        | hd :: .(pref ++ suff)
        | MkSplitAt pref suff = ?a

-- Solution: use (::) defined above
splitAt : (m : Nat) -> (xs : Vect (m + n) a) -> SplitAt m xs
splitAt 0 xs = MkSplitAt [] xs
splitAt (S m) xs@_ with (view xs)
  _ | hd :: tl = hd :: splitAt m tl
