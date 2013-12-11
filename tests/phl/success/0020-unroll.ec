require import Int.

module M = {
  proc f() : unit = {
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
  proc; unroll {1} 2.1.
  admit.
qed.

  