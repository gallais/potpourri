module Data.Singleton

%default total

public export
data Singleton : {0 a : Type} -> (x : a) -> Type where
  MkSingleton : (x : a) -> Singleton x

public export
getSingleton : Singleton {a} x -> a
getSingleton (MkSingleton x) = x

public export
(<$>) : (f : a -> b) -> Singleton x -> Singleton (f x)
f <$> MkSingleton x = MkSingleton (f x)

public export
(<*>) : Singleton f -> Singleton x -> Singleton (f x)
MkSingleton f <*> MkSingleton x = MkSingleton (f x)

export
Show a => Show (Singleton {a} x) where
  show (MkSingleton x) = show x
