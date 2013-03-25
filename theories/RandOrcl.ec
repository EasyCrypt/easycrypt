require import Int.
require import Map.

theory ROM.
  type from.
  type to.

  cnst dsample: to distr.

  (* Signature for random oracles from "from" to "to" *)
  module type RO = {
    fun Init(): unit
    fun O(x:from): to
  }.

  (* Bare random oracle for use in schemes *)
  module RO: RO = { 
    var m:(from,to) map

    fun Init(): unit = {
      m = empty;
    }
  
    fun O(x:from): to = {
      if (!in_dom x m) m.[x] = $dsample;
      return proj (m.[x]);
    }
  }.

  (* Wrapped random oracle for use by the adversary *)
  cnst qO: int.      (* Maximum number of calls by the adversary *)
  cnst default: to. (* Default element to return on error *)

  module ARO = {
    var log: from Set.set

    fun AdvO(x:from): to = {
      var res1: to = default;
      if (Set.mem x log || Set.card log < qO)
        res1 := RO.O(x); 
      return res1;
    }

    fun Init(): unit = {
      log = Set.empty;
      RO.Init(); 
    }
  }.
end ROM.
