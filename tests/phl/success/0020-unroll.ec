require import Int.

module M = {
  fun f() : unit = {
    var x : int = 0;

    if (true) {
      while (x < 10) {
        x = x + 1;
      }
    }
  }
}.

lemma L : equiv[M.f ~ M.f : true ==> true].
proof.
  fun; unroll {1} 2.1.
  admit.
save.

  