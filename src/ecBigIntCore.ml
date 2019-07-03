(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
module type TheInterface = sig
  type zint

  exception Overflow
  exception InvalidString

  val compare : zint -> zint -> int
  val equal   : zint -> zint -> bool
  val sign    : zint -> int
  val hash    : zint -> int

  val le : zint -> zint -> bool
  val lt : zint -> zint -> bool
  val ge : zint -> zint -> bool
  val gt : zint -> zint -> bool

  val zero : zint
  val one  : zint

  val add  : zint -> zint -> zint
  val neg  : zint -> zint
  val sub  : zint -> zint -> zint
  val mul  : zint -> zint -> zint
  val div  : zint -> zint -> zint
  val ediv : zint -> zint -> zint * zint
  val erem : zint -> zint -> zint
  val gcd  : zint -> zint -> zint
  val abs  : zint -> zint
  val pow  : zint ->  int -> zint

  val pred : zint -> zint
  val succ : zint -> zint

  val parity : zint -> [`Even |  `Odd]

  val lshift : zint -> int -> zint
  val rshift : zint -> int -> zint

  val lgand : zint -> zint -> zint
  val lgor  : zint -> zint -> zint
  val lgxor : zint -> zint -> zint

  module Notations : sig
    val ( =^ ) : zint -> zint -> bool
    val ( +^ ) : zint -> zint -> zint
    val ( ~^ ) : zint -> zint
    val ( -^ ) : zint -> zint -> zint
    val ( *^ ) : zint -> zint -> zint
    val ( /^ ) : zint -> zint -> zint

    val ( <=^ ) : zint -> zint -> bool
    val ( <^  ) : zint -> zint -> bool
    val ( >=^ ) : zint -> zint -> bool
    val ( >^  ) : zint -> zint -> bool
  end

  val of_int : int -> zint
  val to_int : zint -> int

  val of_string : string -> zint
  val to_string : zint -> string

  val pp_print : Format.formatter -> zint -> unit

  val to_why3 : zint -> Why3.BigInt.t
end
