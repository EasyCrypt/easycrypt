require import Int.
require import Distr.
require import Pair.

module M = {
  var w:int
  proc f1():unit = {
    var x,y,z : int;
    var b : bool * bool;
    b = (true, true);

    w = $[0 .. 10];
    b = (fst b, false);

    if (fst b) x = 1;
    else y = 2;

  }

  proc f2():unit = {
    var x,y,z : int;
    var b' : bool * bool;
    b' = (true, true);

    if (fst b') x = 1;
    else y = 2;

    w = $[0 .. 10];
    b' = (fst b', false);

  }
}.

equiv foo : M.f1 ~ M.f2 : true ==> ={M.w}.
proof -strict.
 proc.
 seq 1 1 : (b{1} = b'{2}).
  sim.
 conseq [-frame] (_: _ ==> b{1} = b'{2} /\ ={M.w}) => //.
 eager if.
  trivial.
  intros &m0 b1;wp;rnd => //.
  wp;rnd;wp => //.
  wp;rnd;wp => //.
qed.
