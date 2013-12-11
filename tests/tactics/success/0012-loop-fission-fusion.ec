require import Int.
require import Bool.

module M = {
  proc f() : unit = {
    var x : int;
    var y : int;
    var z : int;
    var t : int;

    if (true) {
      x = 1;
      x = 0;
      while (x < 10) {
        y = 1; t = 2; x = x + 1;
      }
    }
  }

  proc g() : unit = {
    var x : int;
    var y : int;
    var z : int;
    var t : int;

    if (true) {
      x = 1;
      x = 0;
      while (x < 10) {
        y = 1; x = x + 1;
      }
      x = 1;
      x = 0;
      while (x < 10) {
        t = 2; x = x + 1;
      }
    }
  }
}.

lemma L : equiv[M.f ~ M.g : true ==> true].
proof.
  proc.
  fission {1} 1.3!2 @ 1, 2.
  fusion  {1} 1.3!2 @ 1, 1.
  fusion  {2} 1.3!2 @ 1, 1.
  fission {2} 1.3!2 @ 1, 2.
  admit.
qed.
