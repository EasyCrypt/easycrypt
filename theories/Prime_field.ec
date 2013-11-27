(* prime fields GF(q) for q prime *)
require Int.

(* the order of field is a prime q *)
op q: int.
axiom q_pos:  Int.(<) 0 q.
(* TODO: Add an axiom asserting primality of q. *)

type gf_q.

op ( * ): gf_q -> gf_q -> gf_q.  (* multiplication modulo q *)
op ( + ): gf_q -> gf_q -> gf_q.  (* addition modulo q *)
op [ - ]: gf_q -> gf_q.          (* the additive inverse *)
op inv: gf_q -> gf_q.            (* the multiplicative inverse *)

op (-) (x y:gf_q): gf_q = x + -y.      (* subtraction modulo q *)
op (/) (x y:gf_q): gf_q = x * (inv y). (* division modulo q for y <> 0 *)


const gf_q0: gf_q. (* zero *)
const gf_q1: gf_q. (* one *)

(** Field axioms, compare "Harrison: Theorem proving with the Real Numbers, p. 10" *)
axiom one_zero: gf_q0 <> gf_q1.

(* Addition/Subtraction *)
axiom gf_q_add_comm: forall (x y:gf_q),
  x + y = y + x.

axiom gf_q_add_assoc: forall (x y z:gf_q),
  x + (y + z) = (x + y) + z.

axiom gf_q_add_unit: forall (x:gf_q),
  gf_q0 + x = x.

axiom gf_q_add_minus: forall (x:gf_q),
  x + -x = gf_q0.

(* Multiplication *)
axiom gf_q_mult_comm: forall (x y:gf_q),
  x * y = y * x.

axiom gf_q_mult_assoc: forall (x y z:gf_q),
  x * (y * z) = (x * y) * z.

axiom gf_q_mult_unit: forall (x:gf_q),
  x * gf_q1 = x.

axiom gf_q_mult_inv: forall (x:gf_q),
  x <> gf_q0 => (x * (inv x)) = gf_q1.

axiom gf_q_distr: forall (x y z:gf_q),
  x * (y + z) = x * y + x * z.

(** Lemmas *)
lemma gf_q_minus (x:gf_q):
  (x - x) = gf_q0.
proof strict.
  by (rewrite /(-) gf_q_add_minus).
qed.

lemma gf_q_add_unit_right (x:gf_q):
  x + gf_q0 = x.
proof strict.
  by rewrite gf_q_add_comm gf_q_add_unit.
qed.

lemma gf_q_mult_zero (x:gf_q):
  x * gf_q0 = gf_q0.
proof strict.
  cut H: x * gf_q0 + x * gf_q0 = x * gf_q0.
    by rewrite -gf_q_distr gf_q_add_unit.
  cut ->: x * gf_q0 = x * gf_q0 + (x * gf_q0 - x * gf_q0).
    by rewrite gf_q_minus gf_q_add_unit_right.
  by rewrite /(-) gf_q_add_assoc H gf_q_add_minus.
qed.

lemma gf_q_mult_minus (x y:gf_q):
  (-x) * y = - (x * y).
proof strict.
  cut ->: (-x) * y = (-x) * y + x * y + (-( x * y)).
    by rewrite -(gf_q_add_assoc _ (x * y)) gf_q_add_minus gf_q_add_unit_right.
  rewrite (gf_q_mult_comm (-x)) (gf_q_mult_comm x) -gf_q_distr.
  by rewrite (gf_q_add_comm (-x)) gf_q_add_minus gf_q_mult_zero  gf_q_add_unit.
qed.

lemma gf_q_mult_minus_right (x y:gf_q):
   y * (-x)= - (y * x).
proof strict.
  by rewrite (gf_q_mult_comm y) (gf_q_mult_comm y)  gf_q_mult_minus.
qed.

lemma nosmt gf_q_minus_minus (x:gf_q):
  -(-x) = x
by [].

lemma gf_q_minus_distr (x y z:gf_q):
  x * (y - z) = x * y - x * z.
proof strict.
  by rewrite /(-) gf_q_distr gf_q_mult_minus_right.
qed.

lemma gf_q_opp_mult (x:gf_q):
  -x = (-gf_q1) * x.
proof strict.
by rewrite gf_q_mult_minus gf_q_mult_comm gf_q_mult_unit.
qed.

lemma gf_q_opp_distr (x y:gf_q):
  -(x + y) = (-x) + (-y).
proof strict.
by rewrite gf_q_opp_mult gf_q_distr -2!gf_q_opp_mult.
qed.

theory Dgf_q.
  require import Distr.
  require import Real.

  op dgf_q: gf_q distr.

  axiom supp_def: forall (s:gf_q),
    in_supp s dgf_q.

  axiom mu_x_def_in: forall (s:gf_q),
    mu_x dgf_q s = 1%r/q%r.

  axiom lossless: weight dgf_q = 1%r.

end Dgf_q.

(** conversion between int and gf_q *)

import Int.

op i_to_gf_q : int -> gf_q.

op gf_q_to_i : gf_q -> int.

axiom gf_q_to_i_pos: forall (x:gf_q),
  0 <= gf_q_to_i x.

axiom gf_q_to_i_smaller: forall (x:gf_q),
  gf_q_to_i x <= q - 1.

axiom gf_q_to_i_inverse: forall (x:int),
  0 <= x => x < q =>
  gf_q_to_i (i_to_gf_q x) = x.

axiom i_to_gf_inverse: forall (x:gf_q),
  i_to_gf_q (gf_q_to_i x) = x.
