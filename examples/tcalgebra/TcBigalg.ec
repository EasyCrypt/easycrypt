pragma +implicits.

(* -------------------------------------------------------------------- *)
require import AllCore List StdOrder.
require import TcMonoid TcRing TcBigop.

import IntOrder.

(* ==================================================================== *)
(* Big sums over an additive group. Mirrors                            *)
(* [theories/algebra/Bigalg.ec:BigZModule] but as a TC section on      *)
(* [addgroup] carriers.                                                *)
(* ==================================================================== *)
section.
declare type t <: addgroup.

(* -------------------------------------------------------------------- *)
lemma sumrD ['a] (P : 'a -> bool) (F1 F2 : 'a -> t) (r : 'a list) :
  (big P F1 r) + (big P F2 r) = big P (fun x => F1 x + F2 x) r.
proof. by rewrite big_split. qed.

(* -------------------------------------------------------------------- *)
lemma sumrN ['a] (P : 'a -> bool) (F : 'a -> t) (r : 'a list) :
  - (big P F r) = big P (fun x => -(F x)) r.
proof.
apply/(big_endo oppr0 opprD).
qed.

(* -------------------------------------------------------------------- *)
lemma sumrB ['a] (P : 'a -> bool) (F1 F2 : 'a -> t) (r : 'a list) :
  (big P F1 r) - (big P F2 r) = big P (fun x => F1 x - F2 x) r.
proof. by rewrite sumrN sumrD; apply/eq_bigr => /=. qed.

(* -------------------------------------------------------------------- *)
lemma sumr_const ['a] (P : 'a -> bool) (x : t) (s : 'a list) :
  big P (fun _ => x) s = intmul x (count P s).
proof. by rewrite big_const intmulpE 1:count_ge0 // -iteropE. qed.

lemma sumri_const (k : t) (n m : int) :
  n <= m => bigi predT (fun _ => k) n m = intmul k (m - n).
proof. by move=> h; rewrite sumr_const count_predT size_range /#. qed.

(* -------------------------------------------------------------------- *)
lemma sumr_undup ['a] (P : 'a -> bool) (F : 'a -> t) (s : 'a list) :
  big P F s = big P (fun a => intmul (F a) (count (pred1 a) s)) (undup s).
proof.
rewrite big_undup; apply/eq_bigr => x _ /=.
by rewrite intmulpE ?count_ge0 iteropE.
qed.

(* -------------------------------------------------------------------- *)
lemma telescoping_sum (F : int -> t) (m n : int) :
  m <= n => F m - F n = bigi predT (fun i => F i - F (i+1)) m n.
proof.
move=> /ler_eqVlt [<<- | hmn].
+ by rewrite big_geq 1:// subrr.
rewrite -sumrB (@big_ltn m n F) 1:// /=.
have heq: n = n - 1 + 1 by ring.
rewrite heq (@big_int_recr (n-1) m) 1:/# -heq /=.
rewrite (@big_reindex _ _ (fun x => x - 1) (fun x => x + 1) (range m (n - 1))) //.
have ->: (transpose Int.(+) 1) = ((+) 1).
+ by apply: fun_ext => x; ring.
have ->: predT \o transpose Int.(+) (-1) = predT by done.
by rewrite /(\o) /= -(@range_addl m n 1) (@addrC _ (F n)) subr_add2r.
qed.

lemma telescoping_sum_down (F : int -> t) (m n : int) :
  m <= n => F n - F m = bigi predT (fun i => F (i+1) - F i) m n.
proof.
move=> hmn; have /= := telescoping_sum (fun i => -F i) _ _ hmn.
by rewrite opprK addrC => ->; apply eq_big => //= i _; rewrite opprK addrC.
qed.

end section.

(* ==================================================================== *)
(* Big sums over a [comring] carrier. Mirrors                          *)
(* [theories/algebra/Bigalg.ec:BigComRing.BAdd] (additive view).        *)
(* ==================================================================== *)
section.
declare type t <: comring.

(* -------------------------------------------------------------------- *)
lemma sumr_1 ['a] (P : 'a -> bool) (s : 'a list) :
  bigA P (fun _ => oner<:t>) s = ofint (count P s).
proof. by apply/sumr_const. qed.

(* -------------------------------------------------------------------- *)
lemma mulr_suml ['a] (P : 'a -> bool) (F : 'a -> t) (s : 'a list) (x : t) :
  (bigA P F s) * x = bigA P (fun i => F i * x) s.
proof. by rewrite big_distrl //; (apply/mul0r || apply/mulrDl). qed.

lemma mulr_sumr ['a] (P : 'a -> bool) (F : 'a -> t) (s : 'a list) (x : t) :
  x * (bigA P F s) = bigA P (fun i => x * F i) s.
proof. by rewrite big_distrr //; (apply/mulr0 || apply/mulrDr). qed.

lemma divr_suml ['a] (P : 'a -> bool) (F : 'a -> t) (s : 'a list) (x : t) :
  (bigA P F s) / x = bigA P (fun i => F i / x) s.
proof. by rewrite mulr_suml; apply/eq_bigr. qed.

(* -------------------------------------------------------------------- *)
lemma sum_pair_dep ['a 'b] (u : 'a -> t) (v : 'a -> 'b -> t) (J : ('a * 'b) list) :
  uniq J =>
    bigA predT (fun (ij : 'a * 'b) => u ij.`1 * v ij.`1 ij.`2) J
  = bigA predT
      (fun i => u i * bigA predT
         (fun ij : _ * _ => v ij.`1 ij.`2)
         (filter (fun ij : _ * _ => ij.`1 = i) J))
      (undup (unzip1 J)).
proof.
move=> uqJ; rewrite big_pair // &(eq_bigr) => /= a _.
by rewrite mulr_sumr !big_filter &(eq_bigr) => -[a' b] /= ->>.
qed.

lemma sum_pair ['a 'b] (u : 'a -> t) (v : 'b -> t) (J : ('a * 'b) list) :
  uniq J =>
    bigA predT (fun (ij : 'a * 'b) => u ij.`1 * v ij.`2) J
  = bigA predT
      (fun i => u i * bigA predT v
        (unzip2 (filter (fun ij : _ * _ => ij.`1 = i) J)))
      (undup (unzip1 J)).
proof.
move=> uqJ; rewrite (@sum_pair_dep u (fun _ => v)) // &(eq_bigr) /=.
by move=> a _ /=; congr; rewrite big_map predT_comp /(\o).
qed.

(* -------------------------------------------------------------------- *)
lemma mulr_big ['a 'b]
    (P : 'a -> bool) (Q : 'b -> bool) (f : 'a -> t) (g : 'b -> t)
    (r : 'a list) (s : 'b list) :
    bigA P f r * bigA Q g s
  = bigA P (fun x => bigA Q (fun y => f x * g y) s) r.
proof.
elim: r s => [|x r ih] s; first by rewrite big_nil mul0r.
rewrite !big_cons; case: (P x) => Px; last by rewrite ih.
by rewrite mulrDl -ih mulr_sumr.
qed.

(* -------------------------------------------------------------------- *)
lemma mulr_const_cond ['a] p (s : 'a list) (c : t) :
  bigM<:'a, t> p (fun _ => c) s = exp c (count p s).
proof.
rewrite big_const -iteropE /exp.
by rewrite IntOrder.ltrNge count_ge0.
qed.

lemma mulr_const ['a] (s : 'a list) (c : t) :
  bigM<:'a, t> predT (fun _ => c) s = exp c (size s).
proof. by rewrite mulr_const_cond count_predT. qed.

(* -------------------------------------------------------------------- *)
lemma subrXX (x y : t) n : 0 <= n =>
  exp x n - exp y n = (x - y) * (bigiA predT (fun i => exp x (n - 1 - i) * exp y i) 0 n).
proof.
case: n => [|n ge0_n _]; first by rewrite !expr0 big_geq // subrr mulr0.
rewrite mulrBl !(big_distrr mulr0 mulrDr).
rewrite big_int_recl // big_int_recr //= !expr0 /=.
rewrite !(mulr1, mul1r) -!exprS // opprD !addrA; congr.
rewrite -addrA sumrB /= big_seq big1 ?addr0 //=.
move=> i /mem_range rg_i; rewrite mulrA -exprS 1:/# mulrCA.
by rewrite -exprS 1:/# subr_eq0; do 2! congr => /#.
qed.

end section.

(* ==================================================================== *)
(* Big sums / products under an ordered domain. Mirrors                *)
(* [theories/algebra/Bigalg.ec:BigOrder].                               *)
(* ==================================================================== *)
require import TcNumber.

section.
declare type t <: tcrealdomain.

lemma ler_sum ['a] (P : 'a -> bool) (F1 F2 : 'a -> t) s :
     (forall a, P a => F1 a <= F2 a)
  => (bigA P F1 s <= bigA P F2 s).
proof.
apply: (@big_ind2 (fun (x y : t) => x <= y)) => //=.
  by apply/ler_add.
qed.

lemma sumr_ge0 ['a] (P : 'a -> bool) (F : 'a -> t) s :
     (forall a, P a => zero <= F a)
  => zero <= bigA P F s.
proof.
move=> h; apply: (@big_ind (fun (x : t) => zero <= x)) => //=.
  by apply/addr_ge0.
qed.

lemma sub_ler_sum ['a] (P1 P2 : 'a -> bool) (F1 F2 : 'a -> t) s :
  (forall x, P1 x => P2 x) =>
  (forall x, P1 x => F1 x <= F2 x) =>
  (forall x, P2 x => !P1 x => zero <= F2 x) =>
  bigA P1 F1 s <= bigA P2 F2 s.
proof.
move => sub_P1_P2 le_F1_F2 pos_F2; rewrite (@bigID P2 _ P1).
have -> : predI P2 P1 = P1 by smt().
by rewrite -(addr0 (bigA P1 F1 s)) ler_add ?ler_sum // sumr_ge0 /#.
qed.

lemma sumr_norm ['a] P (F : 'a -> t) s :
  (forall x, P x => zero <= F x) =>
    bigA P (fun x => `|F x|) s = bigA P F s.
proof.
by move=> ge0_F; apply: eq_bigr => /= a Pa; rewrite ger0_norm /#.
qed.

lemma ler_sum_seq ['a] (P : 'a -> bool) (F1 F2 : 'a -> t) s :
     (forall a, mem s a => P a => F1 a <= F2 a)
  => (bigA P F1 s <= bigA P F2 s).
proof.
move=> h; rewrite !(@big_seq_cond P).
by rewrite ler_sum=> //= x []; apply/h.
qed.

lemma sumr_ge0_seq ['a] (P : 'a -> bool) (F : 'a -> t) s :
     (forall a, mem s a => P a => zero <= F a)
  => zero <= bigA P F s.
proof.
move=> h; rewrite !(@big_seq_cond P).
by rewrite sumr_ge0=> //= x []; apply/h.
qed.

lemma prodr_ge0 ['a] (P : 'a -> bool) (F : 'a -> t) (s : 'a list) :
     (forall a, P a => zero <= F a)
  => zero <= bigM P F s.
proof.
move=> h; apply: (@big_ind (fun (x : t) => zero <= x)) => //=.
  by apply/mulr_ge0.
qed.

lemma prodr_gt0 ['a] (P : 'a -> bool) (F : 'a -> t) (s : 'a list) :
     (forall a, P a => zero < F a)
  => zero < bigM P F s.
proof.
move=> h; apply: (@big_ind (fun (x : t) => zero < x)) => //=.
  by apply/mulr_gt0.
qed.

lemma ler_prod ['a] (P : 'a -> bool) (F1 F2 : 'a -> t) s :
     (forall a, P a => zero <= F1 a <= F2 a)
  => (bigM P F1 s <= bigM P F2 s).
proof.
move=> h; elim: s => [|x s ih]; first by rewrite !big_nil lerr.
rewrite !big_cons; case: (P x)=> // /h [ge0F1x leF12x].
by apply/ler_pmul=> //; apply/prodr_ge0=> a /h [].
qed.

lemma prodr_ge0_seq ['a] (P : 'a -> bool) (F : 'a -> t) (s : 'a list) :
     (forall a, mem s a => P a => zero <= F a)
  => zero <= bigM P F s.
proof.
move=> h; rewrite !(@big_seq_cond P).
by rewrite prodr_ge0=> //= x []; apply/h.
qed.

lemma prodr_gt0_seq ['a] (P : 'a -> bool) (F : 'a -> t) (s : 'a list) :
     (forall a, mem s a => P a => zero < F a)
  => zero < bigM P F s.
proof.
move=> h; rewrite !(@big_seq_cond P).
by rewrite prodr_gt0=> //= x []; apply/h.
qed.

lemma ler_prod_seq ['a] (P : 'a -> bool) (F1 F2 : 'a -> t) s :
     (forall a, mem s a => P a => zero <= F1 a <= F2 a)
  => (bigM P F1 s <= bigM P F2 s).
proof.
move=> h; rewrite !(@big_seq_cond P).
by rewrite ler_prod=> //= x []; apply/h.
qed.

lemma big_normr ['a] P (F : 'a -> t) s :
  `|bigA P F s| <= bigA P (fun x => `|F x|) s.
proof.
elim: s => [|x s ih]; first by rewrite !big_nil normr0.
rewrite !big_cons /=; case: (P x) => // Px.
have /ler_trans := ler_norm_add (F x) (bigA P F s); apply.
by rewrite ler_add2l.
qed.

lemma gt0_prodr_seq ['a] (P : 'a -> bool) (F : 'a -> t) (s : 'a list) :
  (forall (a : 'a), a \in s => P a => zero <= F a) =>
  zero < bigM P F s =>
  (forall (a : 'a), a \in s => P a => zero < F a).
proof.
elim: s => // x s IHs F_ge0; rewrite big_cons.
have {IHs} IHs := IHs _; first by smt().
case: (P x) => [Px F_big_gt0 a a_x_s Pa| nPx /IHs]; 2:smt().
smt(pmulr_gt0<:t> prodr_ge0_seq).
qed.

lemma prodr_eq0 ['a] P (F : 'a -> t) s :
      (exists x, P x /\ x \in s /\ F x = zero)
  <=> bigM<:'a, t> P F s = zero.
proof. split.
+ case=> x [# Px x_in_s z_Fx]; rewrite (@big_rem _ _ _ x) //.
  by rewrite Px /= z_Fx mul0r.
+ elim: s => [|x s ih] /=; 1: by rewrite big_nil oner_neq0.
  rewrite big_cons /=; case: (P x) => Px; last first.
  - by move/ih; case=> y [# Py ys z_Fy]; exists y; rewrite Py ys z_Fy.
  rewrite mulf_eq0; case=> [z_Fx|]; first by exists x.
  by move/ih; case=> y [# Py ys z_Fy]; exists y; rewrite Py ys z_Fy.
qed.

lemma ler_pexpn2r n (x y : t) :
  0 < n => zero <= x => zero <= y => (exp x n <= exp y n) <=> (x <= y).
proof.
move=> gt0_n ge0_x ge0_y; split => [|h]; last first.
- by apply/ler_pexp=> //; apply/ltzW.
case: (x = zero) => [->>|nz_x].
- by rewrite expr0n 1:ltzW.
rewrite -subr_ge0 subrXX 1:ltzW // pmulr_lge0 ?subr_ge0 //=.
rewrite {2}(_ : n = n - 1 + 1) 1:#ring big_int_recr /= 1:/#.
rewrite expr0 /= ltr_spaddr ?mul1r; 1: by rewrite expr_gt0 ltr_neqAle /#.
by rewrite sumr_ge0 => /= i _; rewrite mulr_ge0 ?expr_ge0.
qed.

lemma sum_expr (p : t) n : 0 <= n =>
  (oner - p) * bigiA predT (fun i => exp p i) 0 n = oner - exp p n.
proof.
move=> hn; have /eq_sym := subrXX oner p n hn.
rewrite expr1z // => <-; congr.
by apply: eq_big_int => i _ /=; rewrite expr1z mul1r.
qed.

lemma sum_expr_le (p : t) n :
     0 <= n
  => zero <= p < oner
  => (oner - p) * bigiA predT (fun i => exp p i) 0 n <= oner.
proof.
move=> ge0_n [ge0_p lt1_p]; rewrite sum_expr //.
by rewrite ler_subl_addr ler_paddr // expr_ge0.
qed.

lemma sum_iexpr_le (p : t) n : zero <= p < oner =>
  exp (oner - p) 2 * bigiA predT (fun i => ofint i * exp p i) 0 n <= oner.
proof.
case=> [ge0_p lt1_p]; elim/natind: n => [n le0_n|n ge0_n ih].
+ by rewrite big_geq // mulr0.
rewrite big_ltn 1:/# /= ofint0 mul0r add0r.
pose F := fun j => exp p j + p * ((ofint<:t> j - oner) * exp p (j - 1)).
rewrite (@eq_big_int _ _ _ F) => /= [i [gt0_i lti]|].
- by rewrite /F mulrCA -expr_pred 1:/# mulrBl mul1r addrC subrK.
rewrite -sumrD -mulr_sumr mulrDr.
apply: (ler_trans ((oner - p) + p)); last by rewrite lerr_eq subrK.
apply: ler_add.
- rewrite expr2 -mulrA ler_pimulr 1:subr_ge0 1:ltrW //.
  have le := sum_expr_le p (n+1) _ _ => //; first move=> /#.
  rewrite &(ler_trans _ _ le) ler_wpmul2l 1:subr_ge0 1:ltrW //.
  by rewrite (@big_ltn 0) 1:/# /= expr0 ler_paddl.
rewrite mulrCA ler_pimulr // &(ler_trans _ _ ih).
rewrite ler_wpmul2l; first by rewrite expr_ge0 subr_ge0 ltrW.
rewrite &(lerr_eq) (@big_addn 0 _ 1) &(eq_big_int) /=.
by move=> i [ge0_i _]; rewrite ofintS // addrAC subrr add0r.
qed.

end section.
