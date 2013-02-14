(* -------------------------------------------------------------------- *)
open EcMaps

(* -------------------------------------------------------------------- *)
type symbol  = (* private *) string
type qsymbol = (* private *) symbol list * symbol

type symbols = symbol list

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
val pp_symbol  : symbol EcFormat.pp
val pp_qsymbol : qsymbol EcFormat.pp
