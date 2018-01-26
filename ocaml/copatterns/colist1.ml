type nil
type cons

type _ tag =
  | TNil  : nil  tag
  | TCons : cons tag

type 'a colist =
  { Tag : 'b tag
  ; Pld : ('a, 'b) payload
  }
and ('a, _) payload =
  | Nil  :                   ('a, nil)  payload
  | Cons : 'a * 'a colist -> ('a, cons) payload

let corec argh : int colist with
  | ..#Tag -> TNil
  | ..#Pld -> Cons (1, argh)

(* The error here is not that @TNil@ is incompatible with @Cons@
   but rather that in @'a colist@, the @'b@ of @'b tag@ and of
   @('a, 'b) payload@ is not quantified existentially.

Error: This expression has type nil tag
       but an expression was expected of type a0 = $0 tag
       Type nil is not compatible with type $0
*)
