module Data.Singleton

%default total

public export
data Singleton : {0 a : Type} -> (x : a) -> Type where
  MkSingleton : (x : a) -> Singleton x

%unsafe export
unsafeMkSingleton : (y : a) -> Singleton {a} x
unsafeMkSingleton y = believe_me (MkSingleton y)

export
transport : (0 eq : x === y) -> Singleton x -> Singleton y
transport Refl v = v

public export
interface ProofIrrelevant ty where
  canonical : (0 _ : ty) -> ty
  proofIrrelevant : (t, u : ty) -> canonical t = u

export
ProofIrrelevant Void where
  canonical x impossible
  proofIrrelevant t u impossible

export
ProofIrrelevant Unit where
  canonical x = ()
  proofIrrelevant () () = Refl

public export
byIrrelevance : ProofIrrelevant a => Singleton {a} x
byIrrelevance = transport (proofIrrelevant x x) (MkSingleton (canonical x))

public export
getSingleton : Singleton {a} x -> a
getSingleton (MkSingleton x) = x

public export
pure : (x : a) -> Singleton x
pure = MkSingleton

public export
(<$>) : (f : a -> b) -> Singleton x -> Singleton (f x)
f <$> MkSingleton x = MkSingleton (f x)

public export
(<*>) : Singleton f -> Singleton x -> Singleton (f x)
MkSingleton f <*> MkSingleton x = MkSingleton (f x)

export
Show a => Show (Singleton {a} x) where
  show (MkSingleton x) = show x

export
Cast a b => Cast (Singleton {a} x) b where
  cast (MkSingleton x) = cast x
