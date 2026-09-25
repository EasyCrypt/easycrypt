(* Regression test for #1126: `fel` must see the lvalue of an oracle call
   made outside the oracles (`bad <@ o();`) as a write to `bad`. *)

require import AllCore List StdBigop StdOrder FelTactic.
import Bigreal BRA RealOrder.

module M = {
  var c   : int
  var bad : bool

  proc o() : bool = { c <- c + 1; return true; }

  proc main() : unit = { c <- 0; bad <- false; bad <@ o(); }
}.

lemma fel_bound &m : Pr[M.main() @ &m : M.bad /\ M.c <= 1] <= 0%r.
proof.
fail fel 2 M.c (fun _ => 0%r) 1 (M.bad) [M.o : true].
abort.

lemma real_pr &m : Pr[M.main() @ &m : M.bad /\ M.c <= 1] = 1%r.
proof. by byphoare => //; proc; inline M.o; auto. qed.
