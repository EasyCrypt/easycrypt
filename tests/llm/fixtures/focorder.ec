(* Deliberately truncated, like fixtures/midproof.ec: the file ends on
   `split.`, so a bare LOAD lands with two open goals. The two goals
   need *different* tactics and neither closes the other, so a COMMIT
   that emits them in the wrong order produces a body that does not
   replay. *)
require import AllCore.

lemma focus_order (x y : int) : x = x /\ y + 0 = y.
proof.
split.
