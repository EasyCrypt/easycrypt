require list.

theory PRP_PRF.
  import list.
  print op length.

  type ('a, 'b) map.

  op dom['a 'b] : ('a, 'b) map -> 'a list.
  op codom['a 'b] : ('a, 'b) map -> 'b list.
  op in_dom['a 'b] : ('a, ('a, 'b) map) -> bool.
  op not : bool -> bool.
  op [<] : (int, int) -> bool.
  op [&&] : (bool, bool) -> bool.
  op get['a 'b] : (('a, 'b) map, 'a) -> 'b.
  op set['a 'b] : (('a, 'b) map, 'a, 'b) -> ('a, 'b) map.

  type from.
  type to.
  pop sample : () -> to.
  (* we need a way to express the probabilty of each elements of sample *)
  cnst q : int.
(*  axiom q_pos : 0 < q.  *)

  module type I = {
    proc F (x:from) : to 
  }.

  module type Adv (O:I) = {
    proc A () : bool { D.F }
  }.

  (* Better here to do a declare module *)
  module PRP (FA:Adv) = {
    var m : (from,to) map

    proc F (x:from) : to = {
      var t : to;

      if (not(in_dom(x,m)) && (length(dom(m)) < q)) {
        t = sample();
        if (mem(t,codom(m))) t = sample(); (* \ dom(m)); parse error *)
        m = set(m, x, t); (* m[x] = t; *)
      }
      return get(m, x); (* m[x]; *)
    }

    module PA = { proc F = F }

    module A = FA(PA)
    
    proc Main() : bool = {
      var b : bool;
      m = empty_map;
      b = A();
      return b;
    }
  }.

  module PRP_bad (FA:Adv) = {
    var m : (from,to) map
    var bad : bool

    proc F (x:from) : to = {
      var t : to;

      if (!in_dom(x,m) && length(dom(m)) < q) {
        t = sample();
        if (mem(t,dom(m))) { bad = true; t = sample() (* \ dom(m) *) ;}
        m[x] = t;
      }
      return m[x];
    }

    module PA = { proc F = F }

    module A = FA(PA)
    
    proc Main() : bool = {
      var b : bool;
      bad = true;
      m = empty_map;
      b = A();
      return b;
    }
  }.

  module PRF_bad (FA:Adv) = {
    var m : (from,to) map
    var bad : bool

    proc F (x:from) : to = {
      var t : to;

      if (!in_dom(x,m) && length(dom(m)) < q) {
        t = sample();
        if (mem(t,dom(m))) bad = true;
        m[x] = t;
      }
      return m[x];
    }

    module PA = { proc F = F } 

    module A = FA(PA)
    
    proc Main() : bool = {
      var b : bool;
      bad = true;
      m = empty_map;
      b = A();
      return b;
    }
  }.

  module PRF (FA:Adv) = {

    var m : (from,to) map

    proc G (x:from) : to = {
      var t : to;

      if (!in_dom(x,m) && length(dom(m)) < q) {
        t = sample();
        m[x] = t;
      }
      return m[x];
    }
    
    module FF = { 
      proc F = G
    }

    module A = FA(FF)
    
    proc Main() : bool = {
      var b : bool;
      m = empty_map;
      b = A();
      return b;
    }
  }.

end PRP_PRF.
