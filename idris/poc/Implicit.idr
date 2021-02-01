%default total

prefix 0 #
||| A value together with a proof. The proof ought to be manufactured
||| automatically either because it's been let-bound somewhere or it
||| is trivial by proof search. This allows the user not to bother
||| wrapping it up explicitly.
||| The record constructor is a prefix symbol because it should only
||| ever be applied to a single explicit argument.
record Implicit {a : Type} (p : a -> Type) where
  constructor (#)
  value : a
  {auto 0 proof : p value}

||| Even, as an inductive predicate on natural numbers
data Even : Nat -> Type where
  Zero : Even Z
  SSuc : Even n -> Even (S (S n))

||| To construct a value with a returned implicit proof, we only need
||| to use the Implicit constructor together with the value. Here we
||| return 2 together with the proof it is even.
anEven : Implicit Even
anEven = # 2

||| Inversion result: if 2+n is even then so is n
PPred : Even (S (S n)) -> Even n
PPred (SSuc p) = p

||| Magic function grabing a value available in the context.
it : a => a
it @{p} = p

||| Half is safe to call on even numbers: we will indeed return a value
||| that is half that of the input.
half : (n : Nat) -> {auto 0 _ : Even n} -> Nat
half Z = Z
half (S (S n)) = let 0 p : Even n = PPred it in S (half n)

||| And here we have the implicit in action: we pattern-match on anEven,
||| bringing into scope a value (explicitly) and a proof (implicitly).
||| This allows us to call half.
anHalfEven : Nat
anHalfEven = let (# n) = anEven in half n
