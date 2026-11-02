(* Elimination and matching over indexed inductives.

   - the case/induction scheme GENERATORS (datatype, record, prind,
     projectors) built their type/op occurrences without indices, so
     the schemes were ill-shaped and elim/case failed or anomalied;
   - the matcher tolerated GROUND index mismatches on Fop heads,
     leaking ill-matched instances into InvalidGoalShape downstream. *)

require import AllCore.

type {n} 'a ivec = [ INil | ICons of 'a & 'a ivec<:n> ].

lemma case_ivec {k} (v : int ivec<:k>) :
  v = INil \/ exists x xs, v = ICons x xs.
proof. by case: v => [|x xs]; [left | right; exists x xs]. qed.

lemma elim_ivec {k} (v : int ivec<:k>) : true.
proof. by elim: v. qed.

lemma case_explicit {k} (v : int ivec<:k>) :
  v = INil \/ exists x xs, v = ICons x xs.
proof. elim/ivec_case: v => [|x xs]; [by left | by right; exists x xs]. qed.

(* indexed records: induction scheme *)
type {n} r = { rfld : int ivec<:n> }.

lemma case_r {k} (x : r<:k>) : exists v, x = {| rfld = v |}.
proof. by elim/r_ind: x => v; exists v. qed.

(* indexed inductive predicates *)
type {n} 'a vec.
op vnil {n} ['a] : 'a vec<:n>.

inductive allz {n} (v : int vec<:n>) =
| AllNil of (v = vnil).

lemma elim_allz {k} (v : int vec<:k>) : allz v => v = vnil.
proof. by case. qed.

(* matcher: ground index mismatches fail the match cleanly *)
op f {n} (x : int) : int.
axiom fE3 (x : int) : f[:3] x = 0.

lemma no_ground_confusion (x : int) : f[:5] x = f[:5] x.
proof.
fail rewrite fE3.
trivial.
qed.

axiom fEk {k} (x : int) : f[:k] x = 0.
lemma infer_ok (x : int) : f[:5] x = 0.
proof. by rewrite fEk. qed.
