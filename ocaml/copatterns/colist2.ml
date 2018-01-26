type nil
type cons

type _ tag =
  | TNil  : nil  tag
  | TCons : cons tag

type ('a, 'b) colist =
  { Tag : 'b tag
  ; Pld : ('a, 'b) payload
  }
and ('a, _) payload =
  | Nil  :                         ('a, nil)  payload
  | Cons : 'a * ('a, 'b) colist -> ('a, cons) payload

let corec argh : (int, nil) colist with
  | ..#Tag -> TNil
  | ..#Pld -> Cons (1, argh)

(* If we parameterise @colist@ with @'b@ then the fact that
   the same @b@ is shared between @'b tag@ and @('a, 'b) payload@
   is obvious. But now @argh@'s type annotation betrays the choice
   of @'b@.

   It does catch the obvious bug though:

Error: This expression has type ($1, cons) payload
       but an expression was expected of type a0 = ($1, $2) payload
       Type cons is not compatible with type $2 = nil

*)
