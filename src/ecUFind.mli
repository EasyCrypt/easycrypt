(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
module type Item = sig
  type t

  val equal  : t -> t -> bool
  val compare: t -> t -> int
end

(* -------------------------------------------------------------------- *)
module type Data = sig
  type data
  type effects

  val default   : data
  val isvoid    : data -> bool
  val noeffects : effects
  val union     : data -> data -> data * effects
end

(* -------------------------------------------------------------------- *)
module type S = sig
  type item
  type data
  type effects

  type t

  val initial: t

  val find  : item -> t -> item
  val same  : item -> item -> t -> bool
  val data  : item -> t -> data
  val set   : item -> data -> t -> t
  val isset : item -> t -> bool
  val union : item -> item -> t -> t * effects
  val domain: t -> item list
  val closed: t -> bool
  val opened: t -> int
end

(* -------------------------------------------------------------------- *)
module Make (I : Item) (D : Data)
  : S with type item    = I.t
       and type data    = D.data
       and type effects = D.effects

(* -------------------------------------------------------------------- *)
module type US = sig
  type item
  type t

  val initial : t

  val find  : item -> t -> item
  val union : item -> item -> t -> t
  val same  : item -> item -> t -> bool
end

(* -------------------------------------------------------------------- *)
module UMake (I : Item) : US with type item = I.t
