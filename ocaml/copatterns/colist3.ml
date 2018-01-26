type nil
type cons

type _ tag =
  | TNil  : nil  tag
  | TCons : cons tag

type 'a colist =
  | Wrap : ('a, 'b) tcolist -> 'a colist

and ('a, 'b) tcolist =
  { Tag : 'b tag
  ; Pld : ('a, 'b) payload
  }
and ('a, _) payload =
  | Nil  :                   ('a, nil)  payload
  | Cons : 'a * 'a colist -> ('a, cons) payload

let rec ones : int colist = Wrap
  (let corec tones : (int, cons) tcolist with
        | ..#Tag -> TCons
        | ..#Pld -> Cons (1, ones)
  in tones)

(* And so the ultimate trick is to use a GADT wrapper to indeed
   get an existential.
*)

let head : ('a, cons) payload -> 'a = function
  | Cons (x, _) -> x

let headm : 'a colist -> 'a option = function
  | Wrap t -> match t#Tag with
    | TNil  -> None
    | TCons -> Some (head t#Pld)

let () = print_int (match headm ones with None -> 0 | Some x -> x)
