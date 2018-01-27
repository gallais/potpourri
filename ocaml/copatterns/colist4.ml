type ('a, _) tag =
  | TNil  : ('a, unit) tag
  | TCons : ('a, 'a * 'a colist) tag
and 'a colist =
  { Tag : ('a, 'b) tag
  ; Pld : 'b
  }

let corec argh : int colist with
  | ..#Tag -> TNil
  | ..#Pld -> Cons (1, argh)

(* Same type of error as colist1.ml except that we're using
   a more clever encoding inspired by @gasche's comment:
   https://www.reddit.com/r/haskell/comments/7tbw7d/what_i_whish_i_knew_haskell_and_dependent_pairs/dtbdszv/

Error: This expression has type unit tag
       but an expression was expected of type a0 = $0 tag
       Type unit is not compatible with type $0
*)
