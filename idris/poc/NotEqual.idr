import Data.So

So (not (a == b)) => Uninhabited (the Char a = b) where uninhabited = believe_me
So (not (a == b)) => Uninhabited (the String a = b) where uninhabited = believe_me

record Distinct {a : Type} (x, y : a) where
  constructor MkDistinct
  project : Not (x = y)

%hint
nuke : Uninhabited (a = b) => Distinct a b
nuke = MkDistinct absurd

magic : (0 a : Type) -> (x, y : a) -> {auto _ : Distinct x y} -> Nat
magic _ _ _ = 2

test : Nat
test = magic Char 'a' 'b'

test2 : Nat
test2 = magic String "a" "b"
