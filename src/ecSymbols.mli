(* -------------------------------------------------------------------- *)
open EcMaps

(* -------------------------------------------------------------------- *)
type symbol  = string
type qsymbol = symbol list * symbol
type msymbol = (symbol * msymbol) list

(* -------------------------------------------------------------------- *)
val equal : symbol -> symbol -> bool
val compare : symbol -> symbol -> int

(* -------------------------------------------------------------------- *)
module Msym : Map.S with type key = symbol
module Ssym : Msym.Set

module MMsym : sig
  type +'a t

  val empty  : 'a t
  val add    : symbol -> 'a -> 'a t -> 'a t
  val last   : symbol -> 'a t -> 'a option
  val all    : symbol -> 'a t -> 'a list
  val fold   : (symbol -> 'a list -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val dump :
       name:string
    -> (EcDebug.ppdebug -> 'a -> unit)
    -> EcDebug.ppdebug
    -> 'a t
    -> unit
end

(* -------------------------------------------------------------------- *)
val pp_symbol  : Format.formatter -> symbol -> unit
val pp_qsymbol : Format.formatter -> qsymbol -> unit

