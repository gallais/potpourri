type 'a tree =
  | Node of 'a * 'a tree * 'a tree
  | Leaf

type ('a, 'l, 'r) node =
  | NodeL : ('a, 'a cotree, 'a tree) node
  | NodeR : ('a, 'a tree, 'a cotree) node

and 'a cotree =
  { Cons  : ('a, 'l, 'r) node
  ; Left  : 'l
  ; Right : 'r
  }
