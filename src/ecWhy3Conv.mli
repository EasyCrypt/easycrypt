(* -------------------------------------------------------------------- *)
open Why3

module Talpha : sig
  type t = Term.vsymbol list * Term.term

  val compare : t -> t -> int
end

module Mta : EcMaps.Map.S with type   key = Talpha.t
module Sta : EcMaps.Set.S with type M.key = Talpha.t
