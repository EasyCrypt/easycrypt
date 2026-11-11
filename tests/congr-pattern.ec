(* Tests for the [congr], [congr *] and [congr pat] tactics. *)

require import AllCore.

(* The autodischarge tactic [t_subgoal] used by [congr] tries
   [t_assumption] (alpha) on each generated subgoal. To check that the
   correct subgoals are produced, we therefore avoid having matching
   hypotheses in scope at the point [congr] runs. *)

(* -- regression: bare [congr] still works on f a = f b ---------------- *)
lemma test_default_congr (f : int -> int) (a b : int) :
  a = b => f a = f b.
proof. move=> ?; congr; assumption. qed.

(* -- [congr pat]: one hole; produces exactly [a = c] ----------------- *)
lemma test_pat_one_hole (f : int -> int -> int) (a b c : int) :
  (c = a) => f a b = f c b.
proof.
move=> h; congr (f _ b).
(* the produced subgoal is [a = c]; [h] is [c = a] so plain assumption
   does not close it (no eq_sym auto-orientation). *)
by rewrite h.
qed.

(* -- [congr pat]: two holes; produces [a = c] then [b = d] ----------- *)
lemma test_pat_two_holes (f : int -> int -> int) (a b c d : int) :
  (c = a) /\ (d = b) => f a b = f c d.
proof.
case=> hac hbd.
congr (f _ _).
- by rewrite hac.
- by rewrite hbd.
qed.

(* -- [congr pat]: nested; produces [a = b] --------------------------- *)
lemma test_pat_nested (f g : int -> int) (a b : int) :
  b = a => f (g a) = f (g b).
proof.
move=> h.
congr (f (g _)).
by rewrite h.
qed.

(* -- [congr *]: two diffs; produces [a = a'] then [c = c'] ------------ *)
lemma test_star_two_diffs (f : int -> int -> int -> int) (a a' b c c' : int) :
  (a' = a) /\ (c' = c) => f a b c = f a' b c'.
proof.
case=> haa hcc.
congr *.
- by rewrite haa.
- by rewrite hcc.
qed.

(* -- [congr *]: reflexivity closes when sides are already equal ------- *)
lemma test_star_reflex (f : int -> int) (a : int) :
  f a = f a.
proof. congr *. qed.

(* -- [congr *]: descends through [if] --------------------------------- *)
lemma test_star_if (b : bool) (x x' y y' : int) :
  (x' = x) /\ (y' = y) => (if b then x else y) = (if b then x' else y').
proof.
case=> hx hy.
congr *.
- by rewrite hx.
- by rewrite hy.
qed.

(* -- [congr *]: does NOT descend under a binder ----------------------- *)
lemma test_star_no_binder_descent (P Q : int -> bool) (a : bool) :
  (forall x, Q x) = (forall x, P x) =>
  ((forall x, P x) /\ a) = ((forall x, Q x) /\ a).
proof.
move=> h.
congr *.
by rewrite h.
qed.

(* -- [congr *]: no beta reduction ------------------------------------- *)
(* The two sides have different head shape ([Flambda] applied vs raw
   [Flocal]); since [congr *] never reduces, this leaves the whole
   equality as a single subgoal. *)
lemma test_star_no_beta (a b : int) :
  (b = (fun x => x) a) =>
  ((fun x => x) a = b).
proof. move=> h; congr *; by rewrite h. qed.
