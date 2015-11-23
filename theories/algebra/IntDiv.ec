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
lemma nosmt eqr_sub (x y z t : int) :
  (x - y = z - t) <=> (x + t = z + y).
proof. admit. qed.

lemma nosmt ler_norml x y : (`|x| <= y) <=> (- y <= x <= y).
proof. admit. qed.

lemma nosmt ltr_norml x y : (`|x| < y) <=> (- y < x < y).
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt euclideU d q q' r r':
     0 <= r  < `|d|
  => 0 <= r' < `|d|
  => q * d + r = q' * d + r'
  => q = q' /\ r = r'.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite normr0 ler_lt_asym.
case: (r = r') => [<- /= _ lt_rd /addIr /(mulIf d nz_d)|ne_rr'] //=.
move=> [ge0r lt_rd] [ge0r' lt_r'd]; apply/negP.
rewrite addrC -eqr_sub -mulrBl; move/(congr1 "`|_|")=> eq.
have: `|r - r'| < `|d|; first (rewrite ltr_norml anda_and; split).
+ by rewrite subrE ltr_paddl // ltr_oppr opprK //.
+ by rewrite subrE ltr_naddr // oppr_le0.
rewrite eq normrM gtr_pmull 1:normr_gt0 // (@ltzS _ 0).
rewrite normr_le0 subr_eq0=> ->>; move: eq.
by rewrite subrr normr0P subr_eq0 ne_rr'.
qed.

(* -------------------------------------------------------------------- *)

(* FIXME: re-add when old Int.ec is cleaned up *)
(* op (%%) : int -> int -> int. *)

op (%/) : int -> int -> int.

axiom nosmt edivzP (m d : int):
  m = (m %/ d) * d + (m %% d) /\ (d <> 0 => 0 <= m %% d < `|d|).

axiom divz0 m: m %/ 0 = 0.

(* -------------------------------------------------------------------- *)
lemma nosmt euclideUl d q r m :
     0 <= r < `|d|
  => q * d + r = (m %/ d) * d + (m %% d)
  => q = m %/ d /\ r = m %% d.
proof.
case: (d = 0) => [->|]; first by rewrite ler_lt_asym.
move=> nz_d le_rd eq; apply/(@euclideU d)=> //.
by case: (edivzP m d)=> _ /(_ nz_d).
qed.

(* -------------------------------------------------------------------- *)
lemma modz0 m: m %% 0 = m.
proof. by have [/= <-] := edivzP m 0. qed.

(* -------------------------------------------------------------------- *)
lemma modz_ge0 m d : d <> 0 => 0 <= m %% d.
proof.
case: (d = 0) => [->|nz_d /=]; first by rewrite modz0.
by case: (edivzP m d)=> _ /(_ nz_d) [].
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ltz_mod m d : d <> 0 => m %% d < `|d|.
proof. by move=> gt0_d; case: (edivzP m d) => _ /(_ _) //; rewrite gtr_eqF. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt ltz_pmod m d : 0 < d => m %% d < d.
proof. by move=> ^h /ltr0_neq0 /ltz_mod/(_ m); rewrite gtr0_norm. qed.

(* -------------------------------------------------------------------- *)
lemma div0z d: 0 %/ d = 0.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite divz0.
have /= := euclideUl d 0 0 0; rewrite normr_gt0 nz_d /=.
by have [h _] := (edivzP 0 d); move/(_ h); case=> /eq_sym.
qed.

(* -------------------------------------------------------------------- *)
lemma mod0z d: 0 %% d = 0.
proof. by case: (edivzP 0 d); rewrite div0z /= eq_sym. qed.

(* -------------------------------------------------------------------- *)
lemma divz_eq (m d : int): m = (m %/ d) * d + (m %% d).
proof. by case: (edivzP m d). qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzN (m d : int): m %% (-d) = m %% d.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite oppr0.
have [+ _] := edivzP m (-d); have [+ _] := edivzP m d.
move=> {1}->; rewrite mulrN -mulNr => /eq_sym eq.
have := euclideUl d (- (m %/ -d)) (m %% -d) m.
rewrite modz_ge0 1:oppr_eq0 //= -normrN ltz_mod 1:oppr_eq0 //=.
by move/(_ eq) => [].
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz_abs (m d : int): m %% `|d| = m %% d.
proof.
by case: (d < 0) => [/ltr0_norm|/lerNgt /ger0_norm] ->; rewrite ?modzN.
qed.

(* -------------------------------------------------------------------- *)
lemma edivn_eq d q r: 0 <= r < `|d| => (q * d + r) %/ d = q.
proof. admit. qed.

lemma emodn_eq d q r: 0 <= r < `|d| => (q * d + r) %% d = r.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divz_small m d: 0 <= m < `|d| => m %/ d = 0.
proof. by move=> /edivn_eq /(_ 0). qed.

lemma nosmt modz_small m d: 0 <= m < `|d| => m %% d = m.
proof. by move=> /emodn_eq /(_ 0). qed.

(* -------------------------------------------------------------------- *)
lemma b2i_mod2 b : b2i b %% 2 = b2i b.
proof. by rewrite modz_small //; case: b. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modz_mod m d : m %% d %% d = m %% d.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite modz0.
rewrite -!(modz_abs _ d) modz_small // normr_id ltz_pmod.
  by rewrite normr_gt0. by rewrite modz_ge0 // normr0P.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzDl z1 z2 m: (z1 %% m + z2) %% m = (z1 + z2) %% m by admit.
lemma nosmt modzDr z1 z2 m: (z1 + z2 %% m) %% m = (z1 + z2) %% m by admit.

lemma nosmt modzMml z1 z2 m: ((z1 %% m) * z2) %% m = (z1 * z2) %% m by admit.
lemma nosmt modzMmr z1 z2 m: (z1 * (z2 %% m)) %% m = (z1 * z2) %% m by admit.

lemma nosmt modzMl p d: (p * d) %% d = 0 by admit.
lemma nosmt modzMr p d: (d * p) %% d = 0 by admit.

lemma nosmt modzMDl p m d : (p * d + m) %% d = m %% d by admit.
