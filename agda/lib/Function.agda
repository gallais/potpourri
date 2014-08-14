module lib.Function where

infixl 1 _`_`_
_`_`_ : {A B C : Set} (a : A) (f : (a : A) (b : B) → C) (b : B) → C
a ` f ` b = f a b