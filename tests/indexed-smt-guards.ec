(* SMT relativization guards for indexed types.

   The Why3 translation erases indices at the sort level (word<:3> and
   word<:5> share one sort); soundness requires the index to be
   recoverable at the term level:
   - per-family width observers [size_k : t -> int];
   - quantifiers over head-indexed types are relativized
     ([forall (x : t<:i>), P] ==> [forall x, size x = i => P]);
   - lemma/goal idxvars are guarded by [0 <= n];
   - goal locals and operator results carry their width as facts.

   The two [fail smt] cases below were derivations of [false] before
   the guards existed. *)

require import AllCore List.
require import IArray.

(* Honest width-0 instances of the IArray axioms. *)
lemma hsz0 (c : bool array<:0>) : size (ofarr c) = 0.
proof. by rewrite size_ofarr. qed.

lemma hK0 (c : bool array<:0>) : mkarr (ofarr c) = c.
proof. by rewrite ofarrK. qed.

lemma hnil (s : bool list) : size s = 0 => s = [].
proof. by rewrite size_eq0. qed.

(* Sort erasure alone would let the width-0 lemmas constrain every
   width, collapsing array<:1>. *)
lemma collapse (a b : bool array<:1>) : a = b.
proof.
fail smt(hsz0 hK0 hnil).
abort.

(* An unguarded [forall n : int] quantification of ge0_index would
   assert that every integer is non-negative. *)
lemma negboom (c : bool array<:1>) : false.
proof.
fail smt(ge0_index).
abort.

(* The guards must not break legitimate reasoning: width-0 lemmas
   still apply to width-0 goals (the goal local's size fact discharges
   the relativization premise). *)
lemma ok0 (c : bool array<:0>) : ofarr c = [].
proof. smt(hsz0 hnil). qed.

(* Symbolic-width goals keep working (idxvar 0 <= n facts + guarded
   lemma instantiation at the symbolic width). *)
lemma oksym {n} (a : bool array<:n>) : 0 <= size (ofarr a).
proof. smt(size_ofarr ge0_index). qed.
