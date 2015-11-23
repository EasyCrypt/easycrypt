(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Fun Int IntExtra Ring StdOrder.
(*---*) import Ring.IntID IntOrder.

(* -------------------------------------------------------------------- *)

(* FIXME: re-add when old Int.ec is cleaned up *)
(* op (%%) : int -> int -> int. *)

op (%/) : int -> int -> int.

axiom nosmt edivzP (m d : int):
  m = (m %/ d) * d + (m %% d) /\ (d <> 0 => 0 <= m %% d < `|d|).

axiom divz0 m: m %/ 0 = 0.

(* -------------------------------------------------------------------- *)
lemma modz0 m: m %% 0 = m.
proof. by have [/= <-] := edivzP m 0. qed.

(* -------------------------------------------------------------------- *)
lemma divz_eq (m d : int): m = (m %/ d) * d + (m %% d).
proof. by case: (edivzP m d). qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzN (m d : int): m %% (-d) = m %% d.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzNm z m: (- (z %% m)) %% m = (-z) %% m.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz_abs (m d : int): m %% `|d| = m %% d.
proof.
by case: (d < 0) => [/ltr0_norm|/lerNgt /ger0_norm] ->; rewrite ?modzN.
qed.

(* -------------------------------------------------------------------- *)
lemma modz_ge0 m d : d <> 0 => 0 <= m %% d.
proof.
case: (d = 0) => [->|nz_d /=]; first by rewrite modz0.
by case: (edivzP m d)=> _ /(_ nz_d) [].
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ltz_pmod m d : 0 < d => m %% d < d.
proof.
move=> gt0_d; case: (edivzP m d) => _; rewrite gtr0_norm //.
by move/(_ _)=> //; rewrite gtr_eqF.
qed.

(* -------------------------------------------------------------------- *)
lemma div0z d: 0 %/ d = 0.
proof. admit. qed.

lemma mod0z d: 0 %% d = 0.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma edivn_eq d q r: 0 <= r < `|d| => (q * d + r) %/ d = q.
proof. admit. qed.

lemma emodn_eq d q r: 0 <= r < `|d| => (q * d + r) %% d = r.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divz_small m d: 0 <= m < `|d| => m %/ d = 0.
proof. by move=> /edivn_eq /(_ 0). qed.

lemma nosmt modz_small m d: 0 <= m < d => m %% d = m.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma b2i_mod2 b : b2i b %% 2 = b2i b.
proof. by rewrite modz_small //; case: b. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz_mod m d : m %% d %% d = m %% d.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite modz0.
rewrite -!(modz_abs _ d) modz_small // ltz_pmod ?normr_gt0 //=.
by rewrite modz_ge0 // normr0P.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzDl z1 z2 m: (z1 %% m + z2) %% m = (z1 + z2) %% m by admit.
lemma nosmt modzDr z1 z2 m: (z1 + z2 %% m) %% m = (z1 + z2) %% m by admit.

lemma nosmt modzMml z1 z2 m: ((z1 %% m) * z2) %% m = (z1 * z2) %% m by admit.
lemma nosmt modzMmr z1 z2 m: (z1 * (z2 %% m)) %% m = (z1 * z2) %% m by admit.

lemma nosmt modzMl p d: (p * d) %% d = 0 by admit.
lemma nosmt modzMr p d: (d * p) %% d = 0 by admit.

lemma nosmt modzMDl p m d : (p * d + m) %% d = m %% d by admit.
