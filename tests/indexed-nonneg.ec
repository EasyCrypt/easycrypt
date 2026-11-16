(* The non-negativity discipline: index variables range over the
   NATURALS, and the only terms allowed to instantiate an index are
   built from the context's own index variables.  The fact itself is
   the [Int.ge0_index] axiom (sound in the enforced model); the
   [fail] cases below were derivations of [false]: matching an
   idxvar-premised lemma against a goal over an arbitrary int local
   bound the index to that local. *)

require import AllCore.

type {n} vec.

lemma plus {n} : 0 <= n.
proof. exact ge0_index. qed.

(* an arbitrary int local is NOT an index variable *)
lemma bad (k : int) : 0 <= k.
proof.
fail apply plus.
abort.

(* the axiom itself is gated the same way *)
lemma bad0 (k : int) : 0 <= k.
proof.
fail apply ge0_index.
abort.

(* same through an idxvar-premised axiom *)
type {n} t.
axiom ge0_idx {n} (x : t<:n>) : 0 <= n.

lemma bad2 (k : int) : 0 <= k.
proof.
fail apply (ge0_idx witness).
abort.

(* positive control: a goal whose variable IS an index variable *)
lemma ok {k} : 0 <= k.
proof. apply plus. qed.

(* positive control: index arithmetic over index variables *)
lemma ok2 {k} : 0 <= k + 1.
proof. apply plus. qed.
