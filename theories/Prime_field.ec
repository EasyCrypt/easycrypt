(* prime fields GF(q) for q prime *)
require import Int.
require import Distr.
require import Real.

(* the order of field is a prime q *)
op q: int.
axiom q_pos: 0 < q.
(* TODO: Add an axiom asserting primality of q. *)

type gf_q.

op ( * ): gf_q -> gf_q -> gf_q.  (* multiplication modulo q *)
op ( + ): gf_q -> gf_q -> gf_q.  (* addition modulo q *)
op neg: gf_q -> gf_q.         (* the additive inverse *)
op inv: gf_q -> gf_q.         (* the multiplicative inverse *)

op (-) (x y:gf_q): gf_q = x + (neg y). (* subtraction modulo q *)
op (/) (x y:gf_q): gf_q = x * (inv y). (* division modulo q for y <> 0 *)


op gf_q0: gf_q. (* zero *)
op gf_q1: gf_q. (* one *)

(** Field axioms, compare "Harrison: Theorem proving with the Real Numbers, p. 10" *)
axiom one_zero: gf_q0 <> gf_q1.

(* Addition/Subtraction *)
axiom gf_q_add_comm: forall (x y:gf_q),
  x + y = y + x.

axiom gf_q_add_assoc: forall (x y z:gf_q),
  x + (y + z) = (x + y) + z.

axiom gf_q_add_unit: forall (x:gf_q),
  gf_q0 + x = x.

axiom gf_q_plus_minus: forall (x:gf_q),
  x + (neg x) = gf_q0.

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
lemma gf_q_mult_zero: forall (x:gf_q),
  x * gf_q0 = gf_q0.

lemma gf_q_minus: forall (x:gf_q),
  (x - x) = gf_q0.

lemma gf_q_minus_minus: forall (x:gf_q),
  neg(neg x) = x.

lemma gf_q_mult_minus: forall (x y:gf_q),
  (neg x) * y = neg (x * y).

lemma gf_q_minus_distr: forall (x y z:gf_q),
  x * (y - z) = x * y - x * z.


(** conversion between int and gf_q *)
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

theory Dgf_q.
  op dgf_q: gf_q distr.

  axiom supp_def: forall (s:gf_q),
    in_supp s dgf_q.

  axiom mu_x_def_in: forall (s:gf_q),
    mu_x dgf_q s = 1%r/q%r.

  axiom mu_weight_pos: mu_weight dgf_q = 1%r.

end Dgf_q.

(* some lemmas for testing
lemma a:
forall (a b c d : gf_q), (a + (b + gf_q0)) * c  * gf_q1 = a * c + b * c + (d - d).

lemma b:
forall (a b c d : gf_q),
  a + d <> gf_q0 => 
  (a + (b + gf_q0)) * c + gf_q1 = a * c + b * c + ((a+d) / (a+d)).

lemma c_aux1:
forall (a b c d e w : gf_q), (a * w + b * (e - c * w) + d - b * e - d) = (a * w  - b * c * w + d - d).

lemma c_aux2:
forall (a b c d e w : gf_q), (a * w  - b * c * w + d - d) =  (a * w  - b * c * w).

lemma c_aux3:
  forall (a b c d e w : gf_q),  (a * w + b * (e - c * w) + d - b * e - d) = (a * w  - b * c * w).

lemma c_aux4:
forall (a b c d e w : gf_q), (a * w  - b * c * w) = (w * (a - b * c)).


lemma c:
forall (a b c d e : gf_q), a - b * c <> gf_q0 =>
  forall (w : gf_q), w = inv(a - b * c) * (a * w + b * (e - c * w) + d - b * e - d).
*)