require import Distr. import Dinter.
require import Int. 

module G = {
  fun f() : int = {
    var k : int;
    k = $dinter 0 10;
    return k;
  }
}.

lemma G_in_range:
  hoare [ G.f : true ==> 0 <= res /\ res <= 10 ].
proof.
fun;rnd;skip;smt.
save.
