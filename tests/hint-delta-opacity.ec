require import AllCore.

(* Proof-local, tactic-local and per-call reduction-opacity overrides:
   [-delta op] blocks the delta-reduction of [op], [+delta op] allows it
   even when [op] is declared [opaque]. An explicit unfolding
   ([rewrite /op]) still unfolds. *)

op f (x : int) = x + 1.
op [opaque] h (x : int) = x + 2.

(* [rewrite fE] fails when the goal no longer contains [f 0]: it
   witnesses that [f] was not unfolded. *)
lemma fE : f 0 = 1 by done.

(* --- Sanity ---------------------------------------------------------- *)

lemma f_done : f 0 = 1. proof. done. qed.
lemma h_nodone : h 0 = 2. proof. fail done. by rewrite /h. qed.

(* --- [-delta f]: proof-local ----------------------------------------- *)

(* An explicit unfolding still unfolds. *)
lemma f_unfold : f 0 = 1.
proof. hint -delta f. fail done. rewrite /f. done. qed.

lemma f_local : f 0 = 1.
proof. hint -delta f. fail done. simplify. rewrite fE. done. qed.

(* ... it also applies to the reductions of crush. *)
lemma f_local_crush : f 0 = 1 /\ true.
proof. hint -delta f. fail by move=> />. move=> />. by rewrite fE. qed.

(* --- [-delta f]: tactic-local and per-call --------------------------- *)

lemma f_with : f 0 = 1.
proof. fail with hint -delta f (done). done. qed.

lemma f_call : f 0 = 1.
proof. simplify hint -delta f. rewrite fE. done. qed.

(* --- [+delta h] overrides the [opaque] declaration ------------------- *)

lemma h_local : h 0 = 2.
proof. hint +delta h. done. qed.

lemma h_with : h 0 = 2.
proof. by with hint +delta h (done). qed.
