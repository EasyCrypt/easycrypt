module M = {
  fun f () : int = {
    var y : int;
    y = 1;
    if (y=1) { y = 2; }
    return y;
  }
}.

lemma foo : hoare [M.f : true ==> res = 2 ]
proof.
 fun.
 rcondt 2.
 wp; skip. trivial.
 wp; skip; trivial.
save.
