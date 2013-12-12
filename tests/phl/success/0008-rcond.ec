module M = {
  proc f () : int = {
    var y : int;
    y = 1;
    if (y=1) { y = 2; }
    return y;
  }
}.

lemma foo : hoare [M.f : true ==> res = 2 ].
proof -strict.
 proc.
 rcondt 2.
 wp; skip; smt.
 wp; skip; smt.
qed.
