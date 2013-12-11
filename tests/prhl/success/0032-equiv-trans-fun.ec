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

module M1 = {
  proc f () : int = {
    var x,y : int;
    x = 1;
    return (x+M.w);
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

module M1' = { 
  proc f () : int = {
    var x,y : int;
    y = 2;
    return (y+M'.w);
  }
}.

equiv foo : M.f ~ M'.f : M.w{1} = M'.w{2} + 1 ==> ={res}.
proof.
  transitivity M1.f (={M.w} ==>  ={M.w,res}) 
                    (M.w{1} = M'.w{2} + 1 ==> ={res}).
    intros &m1 &m2 H; exists M.w{m1} => //.
    trivial.
    proc;sim.
  transitivity M1'.f (M.w{1} = M'.w{2} + 1 ==> ={res})
                     (={M'.w} ==> ={M'.w,res}).
    intros &m1 &m2 H; exists M'.w{m2} => //.
    trivial.
  proc;wp;skip;smt.
    proc;sim.
save.
