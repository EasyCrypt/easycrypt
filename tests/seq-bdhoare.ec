require import AllCore Distr DBool.

module M = {
  proc f() : bool = {
    var x, y;
    x <- true;
    y <$ {0,1};
    return x /\ y;
  }
}.

(* No bound information. *)
lemma no_bound : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
seq 1 : (x = true).
+ by wp.
+ by wp; skip.
+ by rnd; skip => />; apply: dbool_ll.
+ by hoare; wp; skip.
by trivial.
qed.

(* Explicit bounds, with the [!r] branch of the prefix bounded by 0: the
   corresponding suffix subgoal is omitted. *)
lemma mult_bounds : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
seq 1 : (x = true) 1%r 1%r 0%r _ (true) => //.
+ by wp.
+ by rnd; skip => />; apply: dbool_ll.
by hoare; wp; skip.
qed.

lemma errors : phoare [M.f : true ==> true] = 1%r.
proof.
proc.
fail seq 1 1 : (x = true).
fail seq{1} 1 : (x = true).
fail seq 1 : (_: true ==> true).
abort.
