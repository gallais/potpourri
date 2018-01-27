
module type AUTORITY = sig

  type 't passport
  type 'a name
  type person = | Name : 'a name -> person

  type ('a, 't) signed = private 'a
  val sign : 't passport -> 'a -> ('a, 't) signed

  module type IDENTITY = sig
    type t
    val name     : t name
    val passport : t passport
  end

  val deliver : person list -> (module IDENTITY)
  val acquire : 't passport -> 'a name -> ('a passport) option

end

module Autority : AUTORITY = struct

  module IntSet = Set.Make(struct
    let compare = Pervasives.compare
    type t = int
  end)

  type 't passport = IntSet.t
  type 'a name     = IntSet.t
  type person = Name : 'a name -> person

  let get_name : person -> IntSet.t = function | Name n -> n

  type ('a, 't) signed = 'a
  let sign _ a = a
  
  module type IDENTITY = sig
    type t
    val name     : t name
    val passport : t passport
  end

  let next_passport = ref 0
  let make_passport = function
    | [] -> let p  = !next_passport in
            let () = next_passport := p+1 in
            IntSet.singleton p
    | ps -> List.fold_left
              (fun s p -> IntSet.union s (get_name p))
              IntSet.empty
              ps

  let deliver ps =
    let passport = make_passport ps in
    (module struct
      type t = unit
      let name = passport
      let passport = passport
    end : IDENTITY)

  let acquire passport name =
    if IntSet.subset passport name
    then Some name
    else None

end
