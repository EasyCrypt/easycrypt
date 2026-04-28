require import AllCore.

notation #pair (a : int) (b : int) "[" a ", " b "] " = (a, b).

module M = {
  proc f (x : int, y : int) : int * int = {
    return (x + 1, y + 1);
  }
}.

(* Notation inside a Hoare post — `res` is the procedure's return value. *)
lemma hoare_ok (a b : int) :
  hoare [M.f : x = a /\ y = b ==> res = #pair [a + 1, b + 1]].
proof.
  proc.
  by trivial.
qed.

(* Probabilistic: same notation in a phoare post. *)
lemma phoare_ok (a b : int) :
  phoare [M.f : x = a /\ y = b ==> res = #pair [a + 1, b + 1]] = 1%r.
proof.
  proc.
  by trivial.
qed.
