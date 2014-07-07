module Monad where

postulate
  M      : Set → Set
  return : {A : Set} (a : A) → M A
  bind   : {A B : Set} (ma : M A) (f : A → M B) → M B

infix -10 do_
infixr -5 doBind

do_ : {A : Set} (ma : M A) → M A
do_ ma = ma

doBind : {A B : Set} (ma : M A) (f : A → M B) → M B
doBind = bind

syntax doBind ma (λ x → f) = x ← ma , f

bind2 : {A B C : Set} (ma : M A) (mb : M B) (f : A → B → M C) → M C
bind2 ma mb f =
  do a ← ma
   , b ← mb
   , f a b