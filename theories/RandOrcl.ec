require import int.
require import map.

theory RndOrcl.

  type from.

  type to.
  
  cnst default : to.

  cnst dsample : to distr.

  module RO = { 
    var m : (from, to) map
  
    fun O (x:from) : to = {
      if (!in_dom x m) m.[x] = $dsample;
      return m.[x];
    }

    fun init () : unit = {
      m = empty default;
    }
  }.

  cnst max_call : int.

  module ARO = { 

    var log : from Set.t

    fun AdvO(x:from) : to = {
      var res : to = default;
      if (!Set.mem x log && Set.card log < max_call)
        res := RO.O(x); 
      return res;
    }

    fun init () : unit = {
      log = Set.empty;
      RO.init (); 
    }
      
  }.


end RndOrcl.

