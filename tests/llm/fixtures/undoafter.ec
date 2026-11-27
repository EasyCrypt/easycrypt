(* An `undo` sits on line 9, right after the line a LOAD stops at.
   Stopping at line 8 must leave the two goals `split.` opened: the
   `undo` is past the stop point and must not run. *)
require import AllCore.

lemma undo_after : 1 = 1 /\ 2 = 2.
proof.
split.
undo 3.
trivial.
