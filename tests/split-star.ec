(* -------------------------------------------------------------------- *)
require import AllCore.

(* `split *` peels every top-level /\ and &&; the right side of && gets
   the left as a hypothesis (matches plain `split` semantics). *)
lemma L1 (a b c d e : bool) :
  a => b => c => d => e =>
  a /\ b /\ (c && d) /\ e.
proof.
move=> ha hb hc hd he.
split *.
+ exact: ha.
+ exact: hb.
+ exact: hc.
+ move=> _; exact: hd.
+ exact: he.
qed.

(* `split +` requires at least one top-level conjunction *)
lemma L2 (a b c d e : bool) :
  a => b => c => d => e =>
  a /\ b /\ (c && d) /\ e.
proof.
move=> ha hb hc hd he.
split +.
+ exact: ha.
+ exact: hb.
+ exact: hc.
+ move=> _; exact: hd.
+ exact: he.
qed.

(* `split *` does NOT descend into other connectives *)
lemma L3 (p q r s : bool) :
  (p => q) => (r \/ s) =>
  (p => q) /\ (r \/ s).
proof.
move=> hpq hrs.
split *.
+ exact: hpq.
+ exact: hrs.
qed.

(* `split *` is a no-op on a non-conjunction goal *)
lemma L4 (p : bool) : p => p.
proof.
move=> hp.
split *.
exact: hp.
qed.

(* `split +` fails on a non-conjunction goal *)
lemma L5 (p : bool) : p => p.
proof.
move=> hp.
fail split +.
exact: hp.
qed.

(* recursing under && carries the left side as a hypothesis to every
   subgoal produced from the right side.  E.g. a && (b /\ c) becomes
   a, a => b, a => c (not a, a => b /\ c). *)
lemma L6 (a b c : bool) :
  a => (a => b) => (a => c) =>
  a && (b /\ c).
proof.
move=> ha hab hac.
split *.
+ exact: ha.
+ exact: hab.
+ exact: hac.
qed.

(* deeper: a && (b && c) becomes a, a => b, a => (b => c) *)
lemma L7 (a b c : bool) :
  a => (a => b) => (a => b => c) =>
  a && (b && c).
proof.
move=> ha hab habc.
split *.
+ exact: ha.
+ exact: hab.
+ exact: habc.
qed.
