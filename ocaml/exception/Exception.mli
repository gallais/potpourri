module type TYPE =
sig
  type t
end

module type EXCEPTION = functor (T : TYPE) ->
sig

  type 'a exn

  val throw : T.t -> 'a exn
  val catch : (T.t -> 'a) -> 'a exn -> 'a

  val pure  : 'a -> 'a exn
  val map   : ('a -> 'b) -> 'a exn -> 'b exn
  val app   : ('a -> 'b) exn -> 'a exn -> 'b exn
  val bind  : 'a exn -> ('a -> 'b exn) -> 'b exn

end
