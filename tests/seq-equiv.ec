require import AllCore.

module M = {
  proc f() : int = {
    var x;
    x <- 1;
    x <- x + 1;
    return x;
  }
}.

lemma two_sided : equiv [M.f ~ M.f : true ==> ={res}].
proof.
proc.
seq 1 1 : (={x} /\ x{1} = 1).
+ by wp; skip.
by wp; skip.
qed.

lemma one_sided_left : equiv [M.f ~ M.f : true ==> res{1} = 2 /\ res{2} = 2].
proof.
proc.
seq{1} 1 : (_: x = 1 ==> x = 2); auto.
qed.

lemma one_sided_right : equiv [M.f ~ M.f : true ==> res{1} = 2 /\ res{2} = 2].
proof.
proc.
seq{2} 1 : (_: x = 1 ==> x = 2); auto.
qed.

lemma errors : equiv [M.f ~ M.f : true ==> ={res}].
proof.
proc.
fail seq 1 : (true).
fail seq{1} 1 : (true).
fail seq{1} 1 1 : (true).
fail seq 1 1 : (_: true ==> true).
abort.
