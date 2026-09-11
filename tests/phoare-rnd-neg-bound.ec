(* pHL `rnd` with an upper bound (upstream #1119): the bound check is lifted
   into the post-condition of a hoare judgment on the statements preceding
   the sampling, which only constrains their terminating runs. The rule must
   also require the bound to be non-negative, on every memory satisfying the
   pre-condition: after the ordinary goal, `0%r <= -1%r` must remain and
   must be unprovable. *)
require import AllCore Distr.

module M = {
  proc f() : unit = { var x : int; while (true) { } x <$ dunit 0; }
}.

lemma bad : phoare[M.f : true ==> true] <= (-1)%r.
proof.
proc.
rnd (fun (_ : int) => true).
+ by while (true); auto.
(* remaining goal: forall &hr, true => 0%r <= -1%r *)
move=> &hr _.
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
(* remaining goal: forall &hr, true => 0%r <= -1%r *)
move=> &hr _.
fail (by smt()).
abort.
