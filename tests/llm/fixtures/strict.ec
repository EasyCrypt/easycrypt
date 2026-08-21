(* Deliberately truncated, under +strict_bullets: the LOAD prefix leaves
   the bullet stack holding `-`, so COMMIT must pick a different token
   for the bullets it emits. *)
pragma +strict_bullets.

require import AllCore.

lemma strict_and : (1 = 1 /\ 2 = 2) /\ 3 = 3.
proof.
split.
- split.
