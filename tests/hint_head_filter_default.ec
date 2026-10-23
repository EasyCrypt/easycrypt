require import AllCore.

(* A proof-local default head filter ([hint -[f]] / [hint +[f]]) must be
   honoured by every simplification path, not only by an explicit
   [simplify]/[cbv]: [/=], [//], [done], [progress], [trivial], [auto]
   and the conversion checks behind [apply]/[exact]. [f] and [g] are
   abstract, so only the user-reduction rules below can reduce them: a
   goal closes only when a rule actually fires, which makes [fail (...)]
   and "the goal is still there afterwards" faithful witnesses. *)

op f : int -> int.
op g : int -> int.

axiom fE (x : int) : f x = x + 1.
axiom gE (x : int) : g x = x + 2.

hint simplify fE.
hint simplify gE.

(* --- Sanity: without a filter, every path fires the rules ----------- *)

lemma nofilter_done     : f 0 = 1. proof. done. qed.
lemma nofilter_slash    : f 0 = 1. proof. by rewrite /=. qed.
lemma nofilter_dslash   : f 0 = 1. proof. by rewrite //. qed.
lemma nofilter_progress : f 0 = 1. proof. by progress. qed.
lemma nofilter_trivial  : f 0 = 1. proof. by trivial. qed.
lemma nofilter_auto     : f 0 = 1. proof. by auto. qed.
lemma nofilter_apply    : f 0 = 1. proof. apply eq_refl. qed.
lemma nofilter_exact    : f 0 = 1. proof. exact eq_refl. qed.

(* --- Exclude filter: the [f]-headed rule is disabled ----------------- *)

(* The explicit tactics already honoured the default filter. *)
lemma exclude_simplify : f 0 = 1.
proof. hint -[f]. simplify. rewrite fE. done. qed.

lemma exclude_cbv : f 0 = 1.
proof. hint -[f]. cbv. rewrite fE. done. qed.

(* [/=] is a bare [simplify]: it must not rewrite [f 0]. *)
lemma exclude_slash : f 0 = 1.
proof. hint -[f]. rewrite /=. rewrite fE. done. qed.

(* [done] must not close the goal. *)
lemma exclude_done : f 0 = 1.
proof. hint -[f]. fail done. rewrite fE. done. qed.

(* ... nor its scoped form. *)
lemma exclude_with_done : f 0 = 1.
proof. fail with hint -[f] (done). done. qed.

(* The non-failing closers must leave the goal open: if any of them had
   closed it, the following [rewrite fE] would have no goal to act on. *)
lemma exclude_dslash : f 0 = 1.
proof. hint -[f]. rewrite //. rewrite fE. done. qed.

lemma exclude_move : f 0 = 1.
proof. hint -[f]. move => //. rewrite fE. done. qed.

lemma exclude_progress : f 0 = 1.
proof. hint -[f]. progress. rewrite fE. done. qed.

lemma exclude_trivial : f 0 = 1.
proof. hint -[f]. trivial. rewrite fE. done. qed.

lemma exclude_auto : f 0 = 1.
proof. hint -[f]. auto. rewrite fE. done. qed.

(* The conversion check of [apply]/[exact] sees the filter too. *)
lemma exclude_apply : f 0 = 1.
proof. hint -[f]. fail (apply eq_refl). rewrite fE. done. qed.

lemma exclude_exact : f 0 = 1.
proof. hint -[f]. fail (exact eq_refl). rewrite fE. done. qed.

(* The other rules are unaffected. *)
lemma exclude_other : g 0 = 2.
proof. hint -[f]. done. qed.

(* The filter is undone by [hint clear default]. *)
lemma exclude_cleared : f 0 = 1.
proof. hint -[f]. fail done. hint clear default. done. qed.

(* --- Include filter: only the [g]-headed rule fires ------------------ *)

lemma include_done : f 0 = 1.
proof. hint +[g]. fail done. rewrite fE. done. qed.

lemma include_slash : f 0 = 1.
proof. hint +[g]. rewrite /=. rewrite fE. done. qed.

lemma include_other : g 0 = 2.
proof. hint +[g]. done. qed.

(* A filter set in one lemma does not leak into the next. *)
lemma no_leak : f 0 = 1.
proof. done. qed.
