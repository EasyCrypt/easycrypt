(* Without the pragma, bullets remain pure decoration (legacy
   behavior). The bullets here would all be misused if strict mode
   were on. *)
require import AllCore.

lemma sloppy (p q : bool) : p => q => p /\ q.
proof.
move=> hp hq; split.
- exact hp.
- exact hq.
qed.

(* Bullet character mismatch is silently accepted in non-strict mode. *)
lemma mixed (p q : bool) : p => q => p /\ q.
proof.
move=> hp hq; split.
- exact hp.
+ exact hq.
qed.
