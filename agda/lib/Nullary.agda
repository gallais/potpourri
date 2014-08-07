module lib.Nullary where

open import Relation.Nullary

dec : ∀ {P C : Set} (d : Dec P) (yes : P → C) (no : ¬ P → C) → C
dec (yes p) y n = y p
dec (no ¬p) y n = n ¬p
