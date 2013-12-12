(* -------------------------------------------------------------------- *)
require import Int.

op x : int * int.
op y : int.

op p : int * int -> bool.

axiom A1 : p x => x = (y, y+1).

lemma L : x = (y, y+1).
proof -strict.
  rewrite A1 1:A1; admit.
qed.

