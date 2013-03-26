require import Int.
require import Map.

type from.
type to.

cnst dsample: to distr. (* Distribution to use on the target type *)
cnst qO: int.           (* Maximum number of calls by the adversary *)
cnst default: to.       (* Default element to return on error by the adversary wrapper *)

(* Signature for random oracles from "from" to "to" *)
module type Oracle = {
  fun init(): unit
  fun o(x:from): to
}.

theory ROM.
  (* Bare random oracle for use in schemes *)
  module RO: Oracle = {
    var m:(from,to) map

    fun init(): unit = {
      m = empty;
    }
  
    fun o(x:from): to = {
      if (!in_dom x m) m.[x] = $dsample;
      return proj (m.[x]);
    }
  }.

  (* Wrapped random oracle for use by the adversary *)
  (* TODO: We would like the following to type as module ARO(RO:Oracle): Oracle = { [...] }. *)
  module ARO(RO:Oracle) = {
    var log: from Set.set

    fun o(x:from): to = {
      var res1: to = default;
      if (Set.mem x log || Set.card log < qO)
        res1 := RO.o(x); 
      return res1;
    }

    fun init(): unit = {
      log = Set.empty;
      RO.init(); 
    }
  }.
end ROM.
