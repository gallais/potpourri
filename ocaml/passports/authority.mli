module type AUTORITY = sig

  (* A person can be mentioned by their name which is tracked at the
     type level by the `name` parameterised type. *)
  type 'a name
  type person = | Name : 'a name -> person

  (* Whenever someone has the passport corresponding to a name, they
     are entitled to sign a value with that name. *)
  type 't passport
  type ('a, 't) signed = private 'a
  val sign : 't passport -> 'a -> ('a, 't) signed

  (* A full identity recognized by the authority consist in a private
     name, a singleton @name@ for it and a @passport@ associated to
     that name. *)
  module type IDENTITY = sig
    type t
    val name     : t name
    val passport : t passport
  end

  (* A group of people can resquest from the authority that they deliver
     to them a joint identity. If the group is empty, the authority will
     simply manufacture a brand new identity. *)
  val deliver : person list -> (module IDENTITY)

  (* Someone can, showing their passport, ask that the authority delivers
     a passport for a joint identity they are a part of. *)
  val acquire : 't passport -> 'a name -> ('a passport) option

end

module Autority : AUTORITY
