(* Regression for the byehoare negative-bound bug.

   Probabilities are non-negative, so `Pr[..] <= -1%r` is absurd. Previously
   `byehoare` accepted it: the real bound was coerced to `xreal` by a coercion
   that silently CLAMPS negatives to 0, degenerating the obligation to
   `pre <= 0` (trivially true for a probability-0 event). Combined with the
   sound `Pr[..:false] = 0%r`, that yielded a proof of `false`.

   The fix always emits an extra real side-condition `0%r <= bd` as a fourth
   goal. Below the first three goals are discharged normally, leaving exactly
   that non-negativity goal, which here is `0%r <= -1%r` -- unprovable, so the
   `done` on it must fail. *)
require import AllCore Distr DBool Xreal.

module M = { proc f() : bool = { return true; } }.

lemma h1 &m : Pr[M.f() @ &m : false] <= -1%r.
proof.
byehoare.
+ proc; auto.
+ smt().
+ move=> &hr; smt().
(* remaining goal: the non-negativity side-condition 0%r <= -1%r *)
fail done.
abort.
