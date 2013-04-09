

require import Distr. import Dinter.

module G = {

  fun f() : int = {
    var k : int;
    k = $dinter 0 10;
    return k;

  }


}.


equiv test : G.f ~ G.f : true ==> res{1}=res{2}
proof.
fun.
rnd.
simplify.
skip.
intros _ _ _ x y H.
assumption.
save.



