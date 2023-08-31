pragma +implicits.

(* -------------------------------------------------------------------- *)
require import AllCore List StdOrder.
require (*--*) Bigop Ring Number.

import Ring.IntID.

(* -------------------------------------------------------------------- *)
abstract theory BigZModule.
clone import Ring.ZModule as ZM.
clear [ZM.* ZM.AddMonoid.*].

clone include Bigop with
  type t <- t,
  op   Support.idm <- ZM.zeror,
  op   Support.(+) <- ZM.(+)

  proof Support.Axioms.*.

realize Support.Axioms.addmA. by apply/addrA. qed.
realize Support.Axioms.addmC. by apply/addrC. qed.
realize Support.Axioms.add0m. by apply/add0r. qed.

(* -------------------------------------------------------------------- *)
lemma sumrD P F1 F2 (r : 'a list):
  (big P F1 r) + (big P F2 r) = big P (fun x => F1 x + F2 x) r.
proof. by rewrite big_split. qed.

(* -------------------------------------------------------------------- *)
lemma sumrN P F (r : 'a list):
  - (big P F r) = (big P (fun x => -(F x)) r).
proof. by apply/(big_endo oppr0 opprD). qed.

(* -------------------------------------------------------------------- *)
lemma sumrB P F1 F2 (r : 'a list):
  (big P F1 r) - (big P F2 r) = big P (fun x => F1 x - F2 x) r.
proof. by rewrite sumrN sumrD; apply/eq_bigr => /=. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt sumr_const (P : 'a -> bool) x s:
  big P (fun _ => x) s = intmul x (count P s).
proof. by rewrite big_const intmulpE 1:count_ge0 // -ZM.AddMonoid.iteropE. qed.

lemma sumri_const k (n m:int) : n <= m => bigi predT (fun _ => k) n m = intmul k (m - n).
proof. by move=> h; rewrite sumr_const count_predT size_range /#. qed.

(* -------------------------------------------------------------------- *)
lemma sumr_undup ['a] (P : 'a -> bool) F s :
  big P F s = big P (fun a => intmul (F a) (count (pred1 a) s)) (undup s).
proof.
rewrite big_undup; apply/eq_bigr=> x _ /=.
by rewrite intmulpE ?count_ge0 ZM.AddMonoid.iteropE.
qed.

lemma telescoping_sum (F: int -> t) (m n:int) : m <= n =>
  F m - F n = bigi predT (fun i => F i - F (i+1)) m n.
proof.
move=> /IntOrder.ler_eqVlt [<<- | hmn].
+ by rewrite big_geq 1:// subrr.
rewrite -sumrB (@big_ltn m n F) 1:// /=.
have heq: n = n - 1 + 1 by ring.
rewrite heq (@big_int_recr (n-1) m) 1:/# -heq /=. 
rewrite (@big_reindex _ _ (fun x=> x - 1) (fun x=> x + 1) (range m (n - 1))) //.
have ->: (transpose Int.(+) 1) = ((+) 1).
+ by apply: fun_ext=> x; ring.
have ->: predT \o transpose Int.(+) (-1) = predT by done.
by rewrite /(\o) /= -(@range_addl m n 1) (@addrC _ (F n)) subr_add2r.
qed. 

lemma telescoping_sum_down (F: int -> t) (m n:int) : m <= n =>
  F n - F m = bigi predT (fun i => F (i+1) - F i) m n.
proof.
move=> hmn; have /= := telescoping_sum (fun i => -F i) _ _ hmn.
by rewrite opprK addrC => ->; apply eq_big => //= i _; rewrite opprK addrC.
qed.

end BigZModule.

(* -------------------------------------------------------------------- *)
abstract theory BigComRing.
clone import Ring.ComRing as CR.
clear [CR.* CR.AddMonoid.* CR.MulMonoid.*].

(* -------------------------------------------------------------------- *)
theory BAdd.
clone include BigZModule with
  type ZM.t <- t,
    op ZM.zeror  <- CR.zeror,
    op ZM.( + )  <- CR.( + ),
    op ZM.([-])  <- CR.([-]),
    op ZM.intmul <- CR.intmul

  proof ZM.* remove abbrev ZM.(-).

realize ZM.addrA. by apply/addrA. qed.
realize ZM.addrC. by apply/addrC. qed.
realize ZM.add0r. by apply/add0r. qed.
realize ZM.addNr. by apply/addNr. qed.

lemma nosmt sumr_1 (P : 'a -> bool) s:
  big P (fun i => oner) s = CR.ofint (count P s).
proof. by apply/sumr_const. qed.

lemma mulr_suml (P : 'a -> bool) F s x :
  (big P F s) * x = big P (fun i => F i * x) s.
proof. by rewrite big_distrl //; (apply/mul0r || apply/mulrDl). qed.

lemma mulr_sumr (P : 'a -> bool) F s x :
  x * (big P F s) = big P (fun i => x * F i) s.
proof. by rewrite big_distrr //; (apply/mulr0 || apply/mulrDr). qed.

lemma divr_suml (P : 'a -> bool) F s x :
  (big P F s) / x = big P (fun i => F i / x) s.
proof. by rewrite mulr_suml; apply/eq_bigr. qed.

lemma nosmt sum_pair_dep ['a 'b] u v J : uniq J =>
    big predT (fun (ij : 'a * 'b) => (u ij.`1 * v ij.`1 ij.`2)%CR) J
  = big predT
      (fun i => u i * big predT
         (fun ij : _ * _ => v ij.`1 ij.`2)
         (filter (fun ij : _ * _ => ij.`1 = i) J))
      (undup (unzip1 J)).
proof.
move=> uqJ; rewrite big_pair // &(eq_bigr) => /= a _.
by rewrite mulr_sumr !big_filter &(eq_bigr) => -[a' b] /= ->>.
qed.

lemma nosmt sum_pair ['a 'b] u v J : uniq J =>
    big predT (fun (ij : 'a * 'b) => (u ij.`1 * v ij.`2)%CR) J
  = big predT
      (fun i => u i * big predT v (unzip2 (filter (fun ij : _ * _ => ij.`1 = i) J)))
      (undup (unzip1 J)).
proof.
move=> uqJ; rewrite (@sum_pair_dep u (fun _ => v)) // &(eq_bigr) /=.
by move=> a _ /=; congr; rewrite big_map predT_comp /(\o).
qed.
end BAdd.

(* -------------------------------------------------------------------- *)
theory BMul.
clone include Bigop with
  type t <- t,
  op   Support.idm <- CR.oner,
  op   Support.(+) <- CR.( * )

  proof Support.*.

realize Support.Axioms.addmA. by apply/mulrA. qed.
realize Support.Axioms.addmC. by apply/mulrC. qed.
realize Support.Axioms.add0m. by apply/mul1r. qed.
end BMul.

(* -------------------------------------------------------------------- *)
lemma mulr_big (P Q : 'a -> bool) (f g : 'a -> t) r s:
    BAdd.big P f r * BAdd.big Q g s
  = BAdd.big P (fun x => BAdd.big Q (fun y => f x * g y) s) r.
proof.
elim: r s => [|x r ih] s; first by rewrite BAdd.big_nil mul0r.
rewrite !BAdd.big_cons; case: (P x) => Px; last by rewrite ih.
by rewrite mulrDl -ih BAdd.mulr_sumr.
qed.

(* -------------------------------------------------------------------- *)
lemma subrXX (x y : t) n : 0 <= n =>
  exp x n - exp y n = (x - y) * (BAdd.bigi predT (fun i => exp x (n - 1 - i) * exp y i) 0 n).
proof.
case: n => [|n ge0_n _]; first by rewrite !expr0 BAdd.big_geq // subrr mulr0.
rewrite mulrBl !(BAdd.big_distrr mulr0 mulrDr).
rewrite BAdd.big_int_recl // BAdd.big_int_recr //= !expr0 /=.
rewrite !(mulr1, mul1r) -!exprS // opprD !addrA; congr.
rewrite -addrA BAdd.sumrB /= BAdd.big_seq BAdd.big1 ?addr0 //=.
move=> i /mem_range rg_i; rewrite mulrA -exprS 1:/# mulrCA. 
by rewrite -exprS 1:/# subr_eq0; do 2! congr => /#.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt mulr_const_cond p s c:
  BMul.big<:'a> p (fun _ => c) s = exp c (count p s).
proof.
rewrite BMul.big_const -MulMonoid.iteropE /exp.
by rewrite IntOrder.ltrNge count_ge0.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt mulr_const s c:
  BMul.big<:'a> predT (fun _ => c) s = exp c (size s).
proof. by rewrite mulr_const_cond count_predT. qed.
end BigComRing.

(* -------------------------------------------------------------------- *)
abstract theory BigOrder.
clone import Number.RealDomain as Num.
clear [Num.*].

import Num.Domain.

clone include BigComRing with
  type CR.t      <- Num.t,
  pred CR.unit   <- Num.Domain.unit,
    op CR.zeror  <- Num.Domain.zeror,
    op CR.oner   <- Num.Domain.oner,
    op CR.( + )  <- Num.Domain.( + ),
    op CR.([-])  <- Num.Domain.([-]),
    op CR.( * )  <- Num.Domain.( * ),
    op CR.invr   <- Num.Domain.invr,
    op CR.intmul <- Num.Domain.intmul,
    op CR.ofint  <- Num.Domain.ofint,
    op CR.exp    <- Num.Domain.exp,
    op CR.lreg   <- Num.Domain.lreg

    proof * remove abbrev CR.(-) remove abbrev CR.(/).

realize CR.addrA     . proof. by apply/Num.Domain.addrA. qed.
realize CR.addrC     . proof. by apply/Num.Domain.addrC. qed.
realize CR.add0r     . proof. by apply/Num.Domain.add0r. qed.
realize CR.addNr     . proof. by apply/Num.Domain.addNr. qed.
realize CR.oner_neq0 . proof. by apply/Num.Domain.oner_neq0. qed.
realize CR.mulrA     . proof. by apply/Num.Domain.mulrA. qed.
realize CR.mulrC     . proof. by apply/Num.Domain.mulrC. qed.
realize CR.mul1r     . proof. by apply/Num.Domain.mul1r. qed.
realize CR.mulrDl    . proof. by apply/Num.Domain.mulrDl. qed.
realize CR.mulVr     . proof. by apply/Num.Domain.mulVr. qed.
realize CR.unitP     . proof. by apply/Num.Domain.unitP. qed.
realize CR.unitout   . proof. by apply/Num.Domain.unitout. qed.

lemma nosmt ler_sum (P : 'a -> bool) (F1 F2 :'a -> t) s:
     (forall a, P a => F1 a <= F2 a)
  => (BAdd.big P F1 s <= BAdd.big P F2 s).
proof.
apply: (@BAdd.big_ind2 (fun (x y : t) => x <= y)) => //=.
  by apply/ler_add.
qed.

lemma nosmt sumr_ge0 (P : 'a -> bool) (F : 'a -> t) s:
     (forall a, P a => zeror <= F a)
  => zeror <= BAdd.big P F s.
proof.
move=> h; apply: (@BAdd.big_ind (fun x => zeror <= x)) => //=.
  by apply/addr_ge0.
qed.

lemma nosmt sub_ler_sum (P1 P2 : 'a -> bool) (F1 F2 : 'a -> t) s : 
  (forall x, P1 x => P2 x) => 
  (forall x, P1 x => F1 x <= F2 x) =>
  (forall x, P2 x => !P1 x => zeror <= F2 x) =>
  BAdd.big P1 F1 s <= BAdd.big P2 F2 s.
proof.
move => sub_P1_P2 le_F1_F2 pos_F2; rewrite (@BAdd.bigID P2 _ P1).
have -> : predI P2 P1 = P1 by smt().
by rewrite -(addr0 (BAdd.big P1 F1 s)) ler_add ?ler_sum // sumr_ge0 /#.
qed.

lemma sumr_norm P F s :
  (forall x, P x => zeror <= F x) =>
    BAdd.big<:'a> P (fun x => `|F x|) s = BAdd.big P F s.
proof.
by move=> ge0_F; apply: BAdd.eq_bigr => /= a Pa; rewrite ger0_norm /#.
qed.

lemma nosmt prodr_ge0 (P : 'a -> bool) F s:
     (forall a, P a => zeror <= F a)
  => zeror <= BMul.big P F s.
proof.
move=> h; apply: (@BMul.big_ind (fun x => zeror <= x)) => //=.
  by apply/mulr_ge0.
qed.

lemma nosmt prodr_gt0 (P : 'a -> bool) F s:
     (forall a, P a => zeror < F a)
  => zeror < BMul.big P F s.
proof.
move=> h; apply: (@BMul.big_ind (fun x => zeror < x)) => //=.
  by apply/mulr_gt0.
qed.

lemma nosmt ler_prod (P : 'a -> bool) (F1 F2 :'a -> t) s:
     (forall a, P a => zeror <= F1 a <= F2 a)
  => (BMul.big P F1 s <= BMul.big P F2 s).
proof.
move=> h; elim: s => [|x s ih]; first by rewrite !BMul.big_nil lerr.
rewrite !BMul.big_cons; case: (P x)=> // /h [ge0F1x leF12x].
by apply/ler_pmul=> //; apply/prodr_ge0=> a /h [].
qed.

lemma nosmt ler_sum_seq (P : 'a -> bool) (F1 F2 :'a -> t) s:
     (forall a, mem s a => P a => F1 a <= F2 a)
  => (BAdd.big P F1 s <= BAdd.big P F2 s).
proof.
move=> h; rewrite !(@BAdd.big_seq_cond P).
by rewrite ler_sum=> //= x []; apply/h.
qed.

lemma nosmt sumr_ge0_seq (P : 'a -> bool) (F : 'a -> t) s:
     (forall a, mem s a => P a => zeror <= F a)
  => zeror <= BAdd.big P F s.
proof.
move=> h; rewrite !(@BAdd.big_seq_cond P).
by rewrite sumr_ge0=> //= x []; apply/h.
qed.

lemma nosmt prodr_ge0_seq (P : 'a -> bool) F s:
     (forall a, mem s a => P a => zeror <= F a)
  => zeror <= BMul.big P F s.
proof.
move=> h; rewrite !(@BMul.big_seq_cond P).
by rewrite prodr_ge0=> //= x []; apply/h.
qed.

lemma nosmt prodr_gt0_seq (P : 'a -> bool) F s:
     (forall a, mem s a => P a => zeror < F a)
  => zeror < BMul.big P F s.
proof.
move=> h; rewrite !(@BMul.big_seq_cond P).
by rewrite prodr_gt0=> //= x []; apply/h.
qed.

lemma gt0_prodr_seq (P : 'a -> bool) (F : 'a -> t) (s : 'a list) : 
  (forall (a : 'a), a \in s => P a => zeror <= F a) => 
  zeror < BMul.big P F s => 
  (forall (a : 'a), a \in s => P a => zeror < F a).
proof.
elim: s => // x s IHs F_ge0; rewrite BMul.big_cons. 
have {IHs} IHs := IHs _; first by smt().
case: (P x) => [Px F_big_gt0 a a_x_s Pa| nPx /IHs]; 2:smt().
smt(pmulr_gt0 prodr_ge0_seq).
qed.

lemma nosmt ler_prod_seq (P : 'a -> bool) (F1 F2 : 'a -> t) s:
     (forall a, mem s a => P a => zeror <= F1 a <= F2 a)
  => (BMul.big P F1 s <= BMul.big P F2 s).
proof.
move=> h; rewrite !(@BMul.big_seq_cond P).
by rewrite ler_prod=> //= x []; apply/h.
qed.

lemma nosmt prodr_eq0 P F s:
      (exists x, P x /\ x \in s /\ F x = zeror)
  <=> BMul.big<:'a> P F s = zeror.
proof. split.
+ case=> x [# Px x_in_s z_Fx]; rewrite (@BMul.big_rem _ _ _ x) //.
  by rewrite Px /= z_Fx Num.Domain.mul0r.
+ elim: s => [|x s ih] /=; 1: by rewrite BMul.big_nil oner_neq0.
  rewrite BMul.big_cons /=; case: (P x) => Px; last first.
  - by move/ih; case=> y [# Py ys z_Fy]; exists y; rewrite Py ys z_Fy.
  rewrite mulf_eq0; case=> [z_Fx|]; first by exists x.
  by move/ih; case=> y [# Py ys z_Fy]; exists y; rewrite Py ys z_Fy.
qed.

lemma ler_pexpn2r n x y :
  0 < n => zeror <= x => zeror <= y => (exp x n <= exp y n) <=> (x <= y).
proof.
move=> gt0_n ge0_x ge0_y; split => [|h]; last first.
- by apply/ler_pexp=> //; apply/ltzW.
case: (x = zeror) => [->>|nz_x].
- by rewrite expr0n 1:ltzW.
rewrite -subr_ge0 subrXX 1:ltzW // pmulr_lge0 ?subr_ge0 //=.
rewrite {2}(_ : n = n - 1 + 1) 1:#ring BAdd.big_int_recr /= 1:/#.
rewrite expr0 /= ltr_spaddr ?mul1r; 1: by rewrite expr_gt0 ltr_neqAle /#.
by rewrite sumr_ge0 => /= i _; rewrite mulr_ge0 ?expr_ge0.
qed.

lemma big_normr ['a] P F s :
  `|BAdd.big<:'a> P F s| <= BAdd.big P (fun x => `|F x|) s.
proof.
elim: s => [|x s ih]; first by rewrite !BAdd.big_nil normr0.
rewrite !BAdd.big_cons /=; case: (P x) => // Px.
have /ler_trans := ler_norm_add (F x) (BAdd.big P F s); apply.
by rewrite ler_add2l.
qed.

lemma sum_expr p n : 0 <= n =>
  (oner - p) * BAdd.bigi predT (fun i => exp p i) 0 n = oner - exp p n.
proof.
move=> hn; have /eq_sym := subrXX oner p n hn.
rewrite expr1z // => <-; congr.
by apply: BAdd.eq_big_int => i _ /=; rewrite expr1z mul1r.
qed.

lemma sum_expr_le p n :
     0 <= n
  => zeror <= p < oner
  => (oner - p) * BAdd.bigi predT (fun i => exp p i) 0 n <= oner.
proof.
move=> ge0_n [ge0_p lt1_p]; rewrite sum_expr //.
by rewrite ler_subl_addr ler_paddr // expr_ge0.
qed.

lemma sum_iexpr_le p n : zeror <= p < oner =>
  exp (oner - p) 2 * BAdd.bigi predT (fun i => ofint i * exp p i) 0 n <= oner.
proof.
case=> [ge0_p lt1_p]; elim/natind: n => [n le0_n|n ge0_n ih].
+ by rewrite BAdd.big_geq // mulr0.
rewrite BAdd.big_ltn 1:/# /= ofint0 mul0r add0r.
pose F := fun j => exp p j + p * ((ofint j - oner) * exp p (j - 1)).
rewrite (@BAdd.eq_big_int _ _ _ F) => /= [i [gt0_i lti]|].
- by rewrite /F mulrCA -expr_pred 1:/# mulrBl mul1r addrC subrK.
rewrite -BAdd.sumrD -BAdd.mulr_sumr mulrDr.
apply: (ler_trans ((oner - p) + p)); last by rewrite lerr_eq subrK.
apply: ler_add.
- rewrite expr2 -mulrA ler_pimulr 1:subr_ge0 1:ltrW //.
  have le := sum_expr_le p (n+1) _ _ => //; first move=> /#.
  rewrite &(ler_trans _ _ le) ler_wpmul2l 1:subr_ge0 1:ltrW //.
  by rewrite (@BAdd.big_ltn 0) 1:/# /= expr0 ler_paddl.
rewrite mulrCA ler_pimulr // &(ler_trans _ _ ih).
rewrite ler_wpmul2l; first by rewrite expr_ge0 subr_ge0 ltrW.
rewrite &(lerr_eq) (@BAdd.big_addn 0 _ 1) &BAdd.eq_big_int /=.
by move=> i [ge0_i _]; rewrite ofintS // addrAC subrr add0r.
qed.

end BigOrder.
