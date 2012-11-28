
theory PRP_PRF.
  type from.
  type to.
  pop sample : () -> to.
  (* we need a way to express the probabilty of each elements of sample *)
  cnst qF : int.
  axiom qF_pos : 0 < q.  

  module type I = {
    fun F (x:from) : to 
  }

  module type Adv (O:I) = {
    fun A () : bool { O.F }
  }

  (* Better here to do a declare module *)
  module PRP (FA:Adv) = {
    var m : (from,to) map
    fun F (x:from) : to = {
      var t : to.
      if (!in_dom(x,m) && length(dom(m)) < q) {
        t = sample();
        if (mem(t,dom(m))) t = sample() \ dom(m);
        m[x] = t;
      }
      return m[x]
    }

    module A = FA(struct fun F = F end)
    
    fun Main() : bool = {
      var b : bool;
      m = empty_map;
      b = A();
      return b;
    }
  }.

  module PRP_bad (FA:Adv) = {
    var m : (from,to) map
    var bad : bool;
    fun F (x:from) : to = {
      var t : to.
      if (!in_dom(x,m) && length(dom(m)) < q) {
        t = sample();
        if (mem(t,dom(m))) { bad = true; t = sample() \ dom(m);}
        m[x] = t;
      }
      return m[x]
    }

    module A = FA(struct fun F = F end)
    
    fun Main() : bool = {
      var b : bool;
      bad = true;
      m = empty_map;
      b = A();
      return b;
    }
  }.

  module PRF_bad (FA:Adv) = {
    var m : (from,to) map
    var bad : bool;
    fun F (x:from) : to = {
      var t : to.
      if (!in_dom(x,m) && length(dom(m)) < q) {
        t = sample();
        if (mem(t,dom(m))) bad = true;
        m[x] = t;
      }
      return m[x]
    }

    module A = FA(struct fun F = F end)
    
    fun Main() : bool = {
      var b : bool;
      bad = true;
      m = empty_map;
      b = A();
      return b;
    }
  }.

  module PRF (FA:Adv) = {

    var m : (from,to) map

    fun G (x:from) : to = {
      var t : to.
      if (!in_dom(x,m) && length(dom(m)) < q) {
        t = sample();
        m[x] = t;
      }
      return m[x]
    }
    
    module FF = { 
      fun F = G
    }

    module A = FA(struct fun F = G end) (* FA(FF) *)
    
    fun Main() : bool = {
      var b : bool;
      m = empty_map;
      b = A();
      return b;
    }
  }.

end.  

