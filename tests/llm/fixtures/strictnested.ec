(* Deliberately truncated, under +strict_bullets: the LOAD prefix leaves
   two frames on the bullet stack (`-` outermost, `+` inside it) and
   four open goals. COMMIT must address the goals still owned by those
   frames with the frames' own tokens, and open one fresh level. *)
pragma +strict_bullets.

require import AllCore.

lemma strict_nested : ((1 = 1 /\ 2 = 2) /\ 3 = 3) /\ 4 = 4.
proof.
split.
- split.
  + split.
