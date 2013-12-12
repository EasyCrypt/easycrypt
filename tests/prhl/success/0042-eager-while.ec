require import Int.
require import Bool.
require import Distr.
require import Map.

module M = {
  var m : (int, int) map

  proc f1 (x:int) : unit = {
    var w:int;
    var b:bool;
    b = true;
    w = $[0..10];
    while (b) { 
      b = ${0,1};
      if (!b) m.[x] = w;
    }
  }

  proc f2 (x:int) : unit = {
    var w:int;
    var b:bool;
    b = true;
    while (b) { 
      b = ${0,1};
      if (!b) {
        m.[x] = $[0..10];
      }
    }
  }
}.

equiv f1_f2 : M.f1 ~ M.f2 : ={M.m,x} ==> ={M.m}.
proof -strict.
 proc.
 sp.
 transitivity{1} 
   {if (b) w = $[0..10]; else w = 0;
    while (b) { 
      b = ${0,1};
      if (!b) M.m.[x] = w;
    } } (={M.m,x,b} /\ b{1} ==> ={M.m})
        (={M.m,x,b} /\ b{1} ==> ={M.m}) => //.
    intros &m1 &m2 [H1 [H2 [H3 H4]]];subst.
    exists true, M.m{m2},  x{m2} => //.
    rcondt{2} 1 => //;sim.
  transitivity{2} {
    while (b) { 
      b = ${0,1};
      if (!b) {
        M.m.[x] = $[0..10];
      }
    }
    if (b) w = $[0..10]; else w = 0; } 
        (={M.m,x,b} /\ b{1} ==> ={M.m})
        (={M.m,x,b} /\ b{1} ==> ={M.m}) => //.
    intros &m1 &m2 [[H1 [H2 H3]] H4];subst.
    exists M.m{m2}, b{m2}, x{m2} => //.
  conseq (_ : ={M.m,b,x} ==> ={M.m,b,x} /\ !b{1}) => //.
    eager while 
      (h: if (b) w = $[0..10]; else w = 0; ~ if (b) w = $[0..10]; else w = 0; :
        ={b} ==> ={w}).
    sim.
    trivial.
    rcondt{1} 1 => //.
    swap{1} 1.
    seq 1 1 : (={M.m,b,x});[ rnd => // | ].
    if{2}.
      rcondt{1} 2; first intros &m;rnd => //.
      rcondf{2} 2; first intros &m;rnd => //.
      wp;rnd => //. 
    rcondt{2} 1 => //.
    wp;rnd;skip;smt.
    sim.
  seq 1 1 : (={M.m});[sim | if{1};[rnd{1};skip;progress => // | wp => //] ].
    smt.
qed.

