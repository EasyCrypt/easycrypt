(* pHL `rnd` with an upper bound (upstream #1119): the bound check is lifted
   into the post-condition of a hoare judgment on the statements preceding
   the sampling, which only constrains their terminating runs. The rule must
   also require the bound to be non-negative; under #1105 a pHL judgment
   with a bound that is negative in some memory is false, so that goal is
   quantified over all memories, unconditionally: after the ordinary goal,
   `0%r <= -1%r` must remain and must be unprovable. *)
require import AllCore Distr.

module M = {
  proc f() : unit = { var x : int; while (true) { } x <$ dunit 0; }
}.

lemma bad : phoare[M.f : true ==> true] <= (-1)%r.
proof.
proc.
rnd (fun (_ : int) => true).
+ by while (true); auto.
(* remaining goal: forall &hr, 0%r <= -1%r *)
move=> &hr.
fail (by smt()).
abort.

(* Same with the event inferred from the post-condition. *)
module N = {
  proc f() : int = { var x : int; while (true) { } x <$ dunit 0; return x; }
}.

lemma bad' : phoare[N.f : true ==> res = 0] <= (-1)%r.
proof.
proc.
rnd.
+ by while (true); auto.
(* remaining goal: forall &hr, 0%r <= -1%r *)
move=> &hr.
fail (by smt()).
abort.

(* Loop-free: the prefix terminates, but the bound is still negative. *)
module L = {
  proc f() : unit = { var y : int; var x : int; y <$ dnull; x <$ dunit 0; }
}.

lemma bad'' : phoare[L.f : true ==> true] <= (-1)%r.
proof.
proc.
rnd (fun (_ : int) => true).
+ by auto=> /> y; rewrite supp_dnull.
(* remaining goal: forall &hr, 0%r <= -1%r *)
move=> &hr.
fail (by smt()).
abort.
