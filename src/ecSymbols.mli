(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcMaps

(* -------------------------------------------------------------------- *)
type symbol  = string
type qsymbol = symbol list * symbol
type msymbol = (symbol * msymbol list) list

(* -------------------------------------------------------------------- *)
val sym_equal   : symbol -> symbol -> bool
val sym_compare : symbol -> symbol -> int

(* -------------------------------------------------------------------- *)
module Msym : Map.S with type key = symbol
module Ssym : Set.S with module M = Map.MakeBase(Msym)

module MMsym : sig
  type +'a t

  val empty  : 'a t
  val add    : symbol -> 'a -> 'a t -> 'a t
  val last   : symbol -> 'a t -> 'a option
  val all    : symbol -> 'a t -> 'a list
  val fold   : (symbol -> 'a list -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val map_at : ('a list -> 'a list) -> symbol -> 'a t -> 'a t
  val iter   : (symbol -> 'a -> unit) -> 'a t -> unit
end

(* -------------------------------------------------------------------- *)
val pp_symbol  : Format.formatter -> symbol  -> unit
val pp_qsymbol : Format.formatter -> qsymbol -> unit
val pp_msymbol : Format.formatter -> msymbol -> unit

val string_of_qsymbol : qsymbol -> string
