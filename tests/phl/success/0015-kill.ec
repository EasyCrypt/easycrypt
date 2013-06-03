require import Int.

module M = {
  fun f(x : int) : int = {
    var y : int;
    var z : int;

    y = 0;
    z = y;
    return y;
  }
}.

lemma L : equiv[M.f ~ M.f : true ==> res{1} = 0]
proof.
  fun; kill {1} 2; admit.
save.


