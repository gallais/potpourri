module Data.RoseTree

import Data.List.Quantifiers

%default total

public export
data Rose : Type -> Type where
  Node : a -> Lazy (List (Rose a)) -> Rose a

parameters
  (0 p : Rose a -> Type)
  (rec : (x : a) -> {ts : Lazy (List (Rose a))} -> All p ts -> p (Node x ts))

  export
  induction  : (t : Rose a) -> p t
  inductions : (ts : List (Rose a)) -> All p ts

  induction (Node x ts) = rec x (inductions ts)

  inductions [] = []
  inductions (t :: ts) = induction t :: inductions ts

export
Functor Rose where
  map f = induction (\_ => Rose _)
        $ \ v, ts => Node (f v) (forget ts)

export
leaf : a -> Rose a
leaf v = Node v []

-- does this even have good properties?
export
join : Rose (Rose a) -> Rose a
join = induction (\ _ => Rose a)
     $ \ (Node v ts), tts => Node v (forget tts ++ ts)
