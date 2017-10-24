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


module Exception : EXCEPTION = functor (T : TYPE) ->
struct

  exception Exc of T.t
  type 'a exn = 'a

  let throw (t : T.t) : 'a exn = raise (Exc t)
  let catch (k : T.t -> 'a) (e : 'a exn) : 'a = try e with Exc t -> k t

  let pure (v : 'a) : 'a exn = v
  let map (f : 'a -> 'b) (t : 'a exn) : 'b exn = f t
  let app (f : ('a -> 'b) exn) (t : 'a exn) : 'b exn = f t
  let bind (t : 'a exn) (f : 'a -> 'b exn) : 'b exn = f t

end

module type MAPEXCEPTION =
  functor (T : TYPE) ->
  functor (U : TYPE) ->
  functor (E : EXCEPTION) ->
  functor (F : EXCEPTION) ->
sig
 val map : (T.t -> U.t) -> 'a E(T).exn -> 'a F(U).exn
end

module MapException : MAPEXCEPTION =
  functor (T : TYPE) ->
  functor (U : TYPE) ->
  functor (E : EXCEPTION) ->
  functor (F : EXCEPTION) ->
struct
  module ET = E(T)
  module FU = F(U)

  let map (f : T.t -> U.t) (a : 'a ET.exn) : 'a FU.exn =
    ET.catch (fun x -> FU.throw (f x)) (ET.map FU.pure a)
end
