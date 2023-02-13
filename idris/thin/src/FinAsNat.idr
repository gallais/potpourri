||| Left as an exercise to the reader in the original paper

module FinAsNat

import Data.Nat
import Data.Nat.Order

%default total

||| A finite number bound by n (Fin n) is defined as
||| 1. its encoding as a Nat
||| 2. a runtime irrelevant proof that the encoding is bound by n
|||    (we reuse the standard library's definition of less-than (LT))
||| This replace the usual definition as an inductive family:
|||
|||   data Fin : Nat -> Type where
|||     Z : Fin (S n)
|||     S : Fin n -> Fin (S n)
export
record Fin (n : Nat) where
  constructor MkFin
  encoding : Nat
  0 valid : encoding `LT` n

||| We can recover the usual Z, S interface by defining smart constructors
namespace Smart

  export
  Z : Fin (S n)
  Z = MkFin 0 (LTESucc LTEZero)

  export
  S : Fin n -> Fin (S n)
  S (MkFin k prf) = MkFin (S k) (LTESucc prf)

||| In order to pattern-match on such finite numbers, we need to define a view.
||| Pattern-matching on a value of type (View k) will reveal whether
||| k was built using Z, or by applying S to a smaller Fin.
public export
data View : Fin n -> Type where
  Z : View Z
  S : (k : Fin n) -> View (S k)

||| The less-than-or-equal relation (LTE) is proof irrelevant
||| This will be useful to us because LT is defined in terms of LTE:
|||   LT m n = LTE (S m) n
irrelevantLTE : (p, q : LTE m n) -> p === q
irrelevantLTE LTEZero LTEZero = Refl
irrelevantLTE (LTESucc p) (LTESucc q) = cong LTESucc (irrelevantLTE p q)

namespace Smart

  ||| Prove that for any finite number, we can compute a view associated to it
  ||| i.e. all Fins are either Z or S-headed.
  export
  view : (k : Fin n) -> View k
  view (MkFin Z (LTESucc prf)) = rewrite irrelevantLTE prf LTEZero in Z
  view (MkFin (S k) (LTESucc prf)) = S (MkFin k prf)
