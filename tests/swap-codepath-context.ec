(* `swap` with a code path (`1.:[1 .. 1]`: then-branch of instruction 1,
   `1?:[1 .. 1]`: else-branch, `2.:[1 .. 1]`: body of the loop at 2) must
   keep the enclosing `if`/`while` and the sibling branch. It used to
   replace the whole program by the addressed block, so the false goals
   below (e.g. `M.f(false)` sets `M.x` to 5) were closed by `auto`/`sim`. *)
require import AllCore.

module M = {
  var x, y : int
  proc f(b : bool) : unit = {
    if (b) { x <- 1; y <- 2; } else { x <- 5; y <- 6; }
  }
  proc w() : unit = {
    x <- 0;
    while (false) { x <- 1; y <- 2; }
  }
  proc g() : unit = { y <- 2; x <- 1; }
}.

lemma then_branch : hoare [M.f : true ==> M.x = 1].
proof.
proc.
fail (swap 1.:[1 .. 1] 1; auto; done).
abort.

lemma else_branch : hoare [M.f : true ==> M.x = 5].
proof.
proc.
fail (swap 1?:[1 .. 1] 1; auto; done).
abort.

lemma while_body : hoare [M.w : true ==> M.x = 1].
proof.
proc.
fail (swap 2.:[1 .. 1] 1; auto; done).
abort.

lemma equiv_side : equiv [M.f ~ M.g : true ==> ={M.x, M.y}].
proof.
proc.
fail (swap{1} 1.:[1 .. 1] 1; by sim).
abort.

(* a reversed range is rejected, with or without a path (it used to be
   accepted as a no-op) *)
lemma reversed_range : hoare [M.f : true ==> true].
proof.
proc.
fail (swap 1.:[3 .. 1] 1).
fail (swap 1?:[3 .. 1] -1).
abort.

(* sanity: a top-level swap still works *)
lemma toplevel : hoare [M.g : true ==> M.x = 1 /\ M.y = 2].
proof. proc. fail (swap [3 .. 1] 1). fail (swap [3 .. 1] -1). swap 1 1. auto. qed.

(* the destination must stay inside the addressed block *)
lemma escape : hoare [M.f : true ==> true].
proof.
proc.
fail (swap 1.:[1 .. 1] 2).
fail (swap 1?:[2 .. 2] -2).
abort.
