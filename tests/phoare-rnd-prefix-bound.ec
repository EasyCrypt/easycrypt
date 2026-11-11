(* pHL `rnd phi d1 d2 d3 d4` (upstream #1124): `phi => mu d E <= d2` and
   `!phi => mu d E <= d4` are checked after the statements preceding the
   sampling, while `d1 * d2 + d3 * d4 <= bd` is checked in the initial
   memory. Bounds `d2` and `d4` that depend on variables written by those
   statements must be rejected. *)
require import AllCore Distr.

module M = {
  proc f(x : bool) : bool = { var b; x <- true; b <$ dunit true; return b; }
}.

(* `d2 = b2r x` is 0 initially, but 1 at the sampling; the judgment is
   false for `x = false` (`M.f` returns `true`). *)
lemma bad : phoare[M.f : !x ==> res] <= (b2r x).
proof.
proc.
fail rnd x 1%r (b2r x) 0%r 1%r.
fail rnd (!x) 0%r 1%r 1%r (b2r x).
abort.

module N = {
  proc f(x : bool) : bool = { var b, y; y <- true; b <$ dunit x; return b; }
}.

(* Bounds that the prefix does not write are fine. *)
lemma ok : phoare[N.f : true ==> res] <= (b2r x).
proof.
proc.
rnd true 1%r (b2r x) 0%r 0%r.
+ by move=> &hr; smt().
+ by auto.
+ by move=> &hr _; rewrite dunitE.
+ by hoare; auto.
+ by move=> &hr.
+ by move=> &hr; smt().
qed.
