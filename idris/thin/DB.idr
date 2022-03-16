module DB

import Data.Bits
import Data.SnocList
import Data.SnocList.AtIndex
import Thin
import Thin.Internal

%default total

record DB {a : Type} (x : a) (sx : SnocList a) where
  constructor MkDB
  index : Nat
  0 atIndex : AtIndex index x sx

%name DB i, j

export
Uninhabited (DB x [<]) where uninhabited (MkDB i p) impossible

export
zero : DB x (sx :< x)
zero = MkDB Z Z

export
succ : DB x sx -> DB x (sx :< y)
succ db = MkDB (S db .index) (S db .atIndex)

public export
data View : DB x sx -> Type where
  Z : View DB.zero
  S : (db : DB x sx) -> View (succ db)

export
view : (db : DB x sx) -> View db
view (MkDB 0 Z) = Z
view (MkDB (S i) (S p)) = S (MkDB i p)

export
lsb : Th (sx :< x) sy -> DB x sy
lsb th = case (view th) of
  Keep th x => zero
  Drop th x => succ (lsb th)

export
Thable (DB x) where
  db *^ th = case view th of
    Done => absurd db
    Drop th x => succ (db *^ th)
    Keep th x => case view db of
      Z => zero
      S db => succ (db *^ th)

export
thicken : Th sx sy -> DB x sy -> Maybe (DB x sx)
thicken th db = case view th of
  Done => absurd db
  Keep th x => case view db of
    Z => pure zero
    S db => succ <$> thicken th db
  Drop th x => case view db of
    Z => Nothing
    S db => thicken th db

-- TODO: take the nat directly rather than sx?
export
asTh : {sx : SnocList a} -> DB x sx -> Th [<x] sx
asTh db = MkTh (length sx) (bit db.index) (bit db.atIndex)
