require import Int.
require import Map.

theory RndOrcl.

  type from.

  type to.
  
  cnst default: to.

  cnst dsample: to distr.

  module RO = { 
    var m:(from,to) map
  
    fun O (x:from): to = {
      if (!in_dom x m) m.[x] = $dsample;
      return proj (m.[x]);
    }

    fun init () : unit = {
      m = empty;
    }
  }.

  cnst max_call : int.

  module ARO = { 

    var log : from Set.set

    fun AdvO(x:from) : to = {
      var res1 : to = default;
      if (!Set.mem x log && Set.card log < max_call)
        res1 := RO.O(x); 
      return res1;
    }

    fun init () : unit = {
      log = Set.empty;
      RO.init (); 
    }
      
  }.

end RndOrcl.

