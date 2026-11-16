(* User rewrite rules (hint simplify) over indexed operator heads.
   Index patterns are matched WITHOUT the unification engine and are
   restricted to the affine single-variable fragment: a constant, a
   bare idxvar [k], or [k + b] (solved as [k := width - b] when the
   width's constant part is at least [b]). *)

require import AllCore.

type {n} vec.

(* ------------------------------------------------------------------ *)
(* Tier 0: bare idxvar patterns.  RHS uses the idxvar as an int TERM
   (dual namespace: the binding seeds both sides). *)
op sz {n} (v : vec<:n>) : int.
axiom szE {n} (v : vec<:n>) : sz v = n.
hint simplify szE.

op v7 : vec<:7>.

lemma t0_concrete : sz v7 = 7.
proof. by simplify. qed.

lemma t0_symbolic {m} (v : vec<:m>) : sz v = m.
proof. by simplify. qed.

(* ------------------------------------------------------------------ *)
(* Constant index patterns fire at that width only. *)
op c3 : vec<:3> -> int.
op cv {n} : vec<:n>.
axiom c3E : c3 cv = 42.
hint simplify c3E.

lemma tc_fires : c3 cv = 42.
proof. by simplify. qed.

(* ------------------------------------------------------------------ *)
(* Tier 1: affine pattern [n + 1].  [t] itself accepts any width; the
   RULE is stated at [n + 1], so it fires only where the width has a
   constant part of at least 1. *)
op t {k} (v : vec<:k>) : int.
axiom tE {n} (v : vec<:n+1>) : t v = 1.
hint simplify tE.

op v8 : vec<:8>.

lemma t1_concrete : t v8 = 1.
proof. by simplify. qed.

lemma t1_symbolic {j} (v : vec<:j+1>) : t v = 1.
proof. by simplify. qed.

(* bare symbolic width: nothing guarantees [m >= 1]; the rule must
   NOT fire ([by simplify] then has nothing to close the goal with) *)
fail lemma t1_nofire {m} (v : vec<:m>) : t v = 1 by simplify.

(* ------------------------------------------------------------------ *)
(* Repeated idxvar: bound at the first index position, checked by
   canonical equality at the second. *)
op dd {n m} : int.
axiom ddE {n} : dd[:n, n] = 0.
hint simplify ddE.

lemma tdup_fires : dd[:3, 3] = 0.
proof. by simplify. qed.

fail lemma tdup_nofire : dd[:3, 4] = 0 by simplify.

(* ------------------------------------------------------------------ *)
(* Declaration-time rejections.  The messages (asserted manually --
   hierror embeds locations, so [expect fail] cannot exact-match):
   - "index arguments in the left-hand side must be a constant, an
      index variable `k', or `k + b' with `b' a constant"
   - "index variable `n' is not bound by an index position of the
      left-hand side" *)

(* out of the affine fragment *)
op q {k} : int.
axiom qE {n} : q[:2 * n] = 0.
fail hint simplify qE.

(* idxvar not recoverable from LHS index positions *)
op g0 : int.
axiom gE {n} : g0 = q[:n].
fail hint simplify gE.

(* ------------------------------------------------------------------ *)
(* Unindexed rules: unchanged behavior. *)
op u : int.
axiom uE : u = 5.
hint simplify uE.

lemma tu : u = 5.
proof. by simplify. qed.
