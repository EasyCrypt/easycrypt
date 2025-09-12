require import AllCore.
require import Distr DBool.

module A = {
  proc f() : bool = {
    var x : bool;
    var garbage : bool;
    garbage <- true;
    x <$ {0,1};
    return x;
  }
  proc g() : bool = {
    var y : bool;
    var garbage : bool;
    garbage <- false;
    y <$ {0,1};
    return y;
  }
}.

(* Simple coupling - just the identical distribution *)
op coupling : (bool * bool) distr = dmap {0,1} (fun b => (b, b)).

lemma test_rndplusplus:
  equiv [ A.f ~ A.g : true ==> res{1} = res{2} ].
proof.
proc.
rndpp coupling.
admit.
admit.
qed.

op f : bool -> bool = (fun b => b).

lemma test_rndplus:
  equiv [ A.f ~ A.f : true ==> res{1} = res{2} ].
proof.
proc.
rndp f.
wp.
by skip => * />.
qed.

