require import Int.
module M = {
  var w : int
  proc f () : int = {
    var x,y : int;
    x = 1;
    y = 2;
    return (x+w);
  }
}.

module M' = { 
  var w : int
  proc f () : int = {
    var x,y : int;
    x = 1;
    y = 2;
    return (y+w);
  }
}.

equiv foo : M.f ~ M'.f : M.w{1} = M'.w{2} + 1 ==> ={res}.
proof.
  proc.
  transitivity {1} { x=1;} (={M.w} ==> ={M.w,x})
                          (M.w{1} = M'.w{2} + 1 ==> x{1} + M.w{1} = y{2} + M'.w{2}).
    intros &m1 &m2 H; exists M.w{m1} => //.
    trivial.
    sim.
  transitivity {2} { y=2;} (M.w{1} = M'.w{2} + 1 ==> x{1} + M.w{1} = y{2} + M'.w{2})
                           (={M'.w} ==> ={M'.w,y}).
    intros &m1 &m2 H; exists M'.w{m2} => //.
    trivial.
  wp;skip;smt.
    sim.                              
save.     



