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
lemma nosmt euclideU d q q' r r':
     q * d + r = q' * d + r'
  => 0 <= r  < `|d|
  => 0 <= r' < `|d|
  => q = q' /\ r = r'.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite normr0 ler_lt_asym.
case: (q' = q) => [-> /addrI ->|ne_qq'] //=; rewrite addrC -eqr_sub.
move/(congr1 "`|_|"); rewrite -mulrBl normrM => eq.
case=> [ge0_r lt_rd] [ge0_r' lr_r'd]; have: `|r - r'| < `|d|.
  rewrite ltr_norml subrE ltr_paddl // 1:ltr_oppr 1:opprK //=.
  by rewrite ltr_naddr // oppr_le0.
rewrite eq gtr_pmull 1:normr_gt0 // (@ltzS _ 0) normr_le0 subr_eq0.
by move=> ->> /=; move: eq; rewrite subrr normr0P subr_eq0.
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
     q * d + r = (m %/ d) * d + (m %% d)
  => 0 <= r < `|d|
  => q = m %/ d /\ r = m %% d.
proof.
case: (d = 0) => [->|]; first by rewrite ler_lt_asym.
move=> nz_d eq le_rd; apply/(@euclideU d)=> //.
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
lemma edivz_eq d q r:
  0 <= r < `|d| => (q * d + r) %/ d = q.
proof.
move=> lt_rd; have [+ _] := (edivzP (q * d + r) d).
by move/euclideUl/(_ lt_rd)=> [<-].
qed.

(* -------------------------------------------------------------------- *)
lemma emodz_eq d q r: 0 <= r < `|d| => (q * d + r) %% d = r.
proof.
move=> lt_rd; have [+ _] := (edivzP (q * d + r) d).
by move/euclideUl/(_ lt_rd)=> [_ <-].
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divz_small m d: 0 <= m < `|d| => m %/ d = 0.
proof. by move=> /edivz_eq /(_ 0). qed.

lemma nosmt modz_small m d: 0 <= m < `|d| => m %% d = m.
proof. by move=> /emodz_eq /(_ 0). qed.

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
lemma modzE m d : m %% d = m - (m %/ d) * d.
proof. by have [+ _] - {2}-> := edivzP m d; rewrite subrE addrAC addrN. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt divzMDl q m d : d <> 0 => (q * d + m) %/ d = q + (m %/ d).
proof.
move=> nz_d; have [+ /(_ nz_d) lt_md] - {1}-> := edivzP m d.
by rewrite addrA -mulrDl edivz_eq.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzMDl p m d : (p * d + m) %% d = m %% d.
proof.
case: (d = 0) => [->|nz_d]; first by rewrite mulr0 add0r.
rewrite modzE divzMDl // mulrDl subrE opprD addrACA.
by rewrite addrN /= -subrE -modzE.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzDl m d : (d + m) %% d = m %% d.
proof. by rewrite -{1}(@mul1r d) modzMDl. qed.

lemma nosmt modzDr m d : (m + d) %% d = m %% d.
proof. by rewrite addrC modzDl. qed.

lemma nosmt modzz d : d %% d = 0.
proof. by rewrite -{1}(@addr0 d) modzDl mod0z. qed.

lemma nosmt modzMl p d : (p * d) %% d = 0.
proof. by rewrite -(@addr0 (p*d)) modzMDl mod0z. qed.

lemma nosmt modzMr p d : (d * p) %% d = 0.
proof. by rewrite mulrC modzMl. qed.

lemma nosmt modzDml m n d : (m %% d + n) %% d = (m + n) %% d.
proof. by rewrite {2}(divz_eq m d) -addrA modzMDl. qed.

lemma nosmt modzDmr m n d : (m + n %% d) %% d = (m + n) %% d.
proof. by rewrite !(addrC m) modzDml. qed.

lemma nosmt modzDm m n d : (m %% d + n %% d) %% d = (m + n) %% d.
proof. by rewrite modzDml modzDmr. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt modzMml m n d : ((m %% d) * n) %% d = (m * n) %% d.
proof. by rewrite {2}(divz_eq m d) mulrDl mulrAC modzMDl. qed.

lemma modzMmr m n d : (m * (n %% d)) %% d = (m * n) %% d.
proof. by rewrite !(mulrC m) modzMml. qed.
