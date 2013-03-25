require import Int.
require import Map.

theory ROM.
  type from.
  type to.

  cnst dsample: to distr.

  (* Signature for random oracles from "from" to "to" *)
  module type RO = {
    fun init(): unit
    fun o(x:from): to
  }.

  (* Bare random oracle for use in schemes *)
  module RO: RO = { 
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
  cnst qO: int.      (* Maximum number of calls by the adversary *)
  cnst default: to. (* Default element to return on error *)

  module ARO: RO = {
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
