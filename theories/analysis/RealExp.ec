(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore StdRing StdOrder RealFun.
(*---*) import IntOrder RField RealOrder.
require import List.

(* -------------------------------------------------------------------- *)
op exp : real -> real.
op ln  : real -> real.

axiom exp0     : exp 0%r = 1%r.
axiom expD     : forall (x y : real), exp (x + y) = exp x * exp y.
axiom exp_mono : forall (x y : real), (exp x <= exp y) <=> (x <= y).
axiom exp_gt0  : forall x, 0%r < exp x.
axiom ln_le0   : forall x, x <= 0%r => ln x = 0%r.

axiom lnK  : forall x, ln (exp x) = x.
axiom expK : forall x, 0%r < x => exp (ln x) = x.

axiom nosmt le_ln_up (x : real): 0%r < x => ln x <= x - 1%r.
axiom nosmt le_ln_dw (x : real): 1%r < x => (x - 1%r) / x < ln x.

axiom nosmt le1Dx_exp (x : real): 0%r <= x => 1%r+x <= exp x.

axiom nosmt convexe_exp a b: convexe exp a b.

op log (a : real) = fun x => ln x / ln a.

op log10 x = log 10%r x.
op log2  x = log  2%r x.

op e : real = exp 1%r.

axiom ge2_e : 2%r <= e.
axiom lt3_e : e < 3%r.

lemma nosmt e_boundW : 2%r <= e <= 3%r.
proof. by rewrite ge2_e /= ltrW ?lt3_e. qed.

lemma nosmt e_gt0 : 0%r < e.
proof. by apply/(@ltr_le_trans 2%r)/ge2_e. qed.

lemma nosmt e_ge0 : 0%r <= e.
proof. by apply/ltrW/e_gt0. qed.

hint exact : e_gt0 e_ge0.

lemma nosmt exp_neq0 x : exp x <> 0%r.
proof. by have := (exp_gt0 x); rewrite ltr_neqAle eq_sym => -[]. qed.

lemma nosmt ln0 : ln 0%r = 0%r.
proof. by rewrite ln_le0. qed.

lemma nosmt inj_exp : injective exp.
proof. by apply/mono_inj/exp_mono. qed.

lemma nosmt expN (x : real) : exp (- x) = inv (exp x).
proof.
apply/(mulfI _ (exp_neq0 x)); rewrite -expD addrN exp0.
by rewrite mulrV // exp_neq0.
qed.

lemma nosmt exp_mono_ltr (x y : real): (exp x < exp y) <=> (x < y).
proof. by apply/lerW_mono/exp_mono. qed.

lemma nosmt ln_mono (x y : real):
  0%r < x => 0%r < y => (ln x <= ln y) <=> (x <= y).
proof. by move=> gt0x gt0y; rewrite -exp_mono !expK. qed.

lemma nosmt ln_mono_ltr (x y : real):
  0%r < x => 0%r < y => (ln x < ln y) <=> (x < y).
proof. by move=> gt0x gt0y; rewrite -exp_mono_ltr !expK. qed.

lemma nosmt ln1 : ln 1%r = 0%r.
proof. by rewrite -exp0 lnK. qed.

lemma nosmt ln_gt0 x : 1%r < x => 0%r < ln x.
proof. by move=> h; rewrite -ln1 ln_mono_ltr //#. qed.

lemma nosmt lnM (x y : real) : 0%r < x => 0%r < y =>
  ln (x * y) = ln x + ln y.
proof.
move=> gt0x gt0y; apply/inj_exp; rewrite expK ?pmulr_lgt0 //.
by rewrite expD !expK.
qed.

lemma nosmt lnV (x : real) : 0%r < x => ln (inv x) = -(ln x).
proof. by move=> gt0x; apply/inj_exp; rewrite expN !expK ?invr_gt0. qed.

lemma nosmt ln_ge0 (x:real): 1%r <= x => 0%r <= ln x.
proof. by move=> ge1x; rewrite -exp_mono exp0 expK // (ltr_le_trans 1%r). qed.

(* -------------------------------------------------------------------- *)
op ( ^ ) (x a : real) =
  if x <= 0%r then b2r (a = 0%r) else exp (a * ln x).

(* -------------------------------------------------------------------- *)
lemma rpowE (x a : real) : 0%r < x => x^a = exp (a * ln x).
proof. by rewrite /(^) ltrNge => ->. qed.

lemma nosmt rpoweE (a : real) : e^a = exp a.
proof. by rewrite rpowE 1:e_gt0 // lnK mulr1. qed.

(* -------------------------------------------------------------------- *)
lemma rpow0 x : x^0%r = 1%r.
proof. by rewrite /(^); case: (x <= 0%r)=> // _; rewrite mul0r exp0. qed.

lemma rpow1 x : 0%r < x => x^1%r = x.
proof. by move=> gt0x; rewrite rpowE // mul1r expK. qed.

(* -------------------------------------------------------------------- *)
lemma rpow0r n : 0%r^n = b2r (n = 0%r).
proof. by rewrite /(^) lerr /=. qed.

lemma rpow1r n : 1%r^n = 1%r.
proof. by rewrite rpowE // ln1 mulr0 exp0. qed.

(* -------------------------------------------------------------------- *)
lemma rpoweK (x : real) : 0%r < x => e^(ln x) = x.
proof. by rewrite rpoweE; apply/expK. qed.

lemma rpowe_mono (n m:real): e^n <= e^m <=> n <= m.
proof. by rewrite !rpoweE exp_mono. qed.

lemma rpowe_hmono (n m:real): n <= m => e^n <= e^m.
proof. by rewrite rpowe_mono. qed.

(* -------------------------------------------------------------------- *)
lemma rpow_gt0 (x n : real): 0%r < x => 0%r < x^n.
proof. by move/rpowE=> ->; apply/exp_gt0. qed.

lemma rpow_ge0 (x n : real): 0%r <= x => 0%r <= x^n.
proof.
rewrite ler_eqVlt => -[<-|/rpow_gt0 /(_ n) /ltrW] //.
by rewrite rpow0r; case: (n = 0%r).
qed.

(* -------------------------------------------------------------------- *)
lemma rpowN (x n : real) : 0%r <= x => x^(-n) = inv (x ^ n).
proof.
rewrite ler_eqVlt=> -[<-|]; first rewrite !rpow0r oppr_eq0.
  by case: (n = 0%r); rewrite !(RField.invr0, RField.invr1).
by move=> gt0x; rewrite !rpowE // mulNr expN.
qed.

lemma rpowD (x n m : real) : 0%r < x => x^(n + m) = x^n * x^m.
proof. by move=> gt0x; rewrite !rpowE // mulrDl expD. qed.

lemma rpowB (x n m : real) : 0%r < x => x^(n - m) = x^n / x^m.
proof. by move=> gt0x; rewrite !(rpowN, rpowD) // ltrW. qed.

lemma rpowM (x n m : real) : 0%r < x => x^(n * m) = (x ^ n) ^ m.
proof. by move=> gt0x; rewrite !rpowE ?exp_gt0 // lnK mulrCA mulrA. qed.

lemma rpowMr (x y n : real) :
  0%r < x => 0%r < y => (x * y)^n = x^n * y^n.
proof.
move=> gt0x gt0y; rewrite !rpowE 1:pmulr_rgt0 //.
by rewrite lnM // mulrDr expD.
qed.

lemma rpowVr (x n : real) : 0%r < x => (inv x)^n = inv (x^n).
proof. by move=> gt0x; rewrite !rpowE ?invr_gt0 ?lnV // mulrN expN. qed.

lemma rpowMVr (x y n : real):
  0%r < x => 0%r < y => (x/y)^n = x^n/y^n.
proof. by move=> gt0x gt0y; rewrite rpowMr ?invr_gt0 // rpowVr. qed.

lemma rpow_nat x n : 0 <= n => 0%r <= x => x^(n%r) = x^n.
proof.
elim: n=> [|n ge0n ih] ge0x; first by rewrite expr0 rpow0.
rewrite exprS // fromintD; move: ge0x.
rewrite ler_eqVlt=> -[<-|]; first rewrite (mul0r 0%r).
  by rewrite rpow0r -fromintD eq_fromint /#.
by move=> gt0x; rewrite rpowD // rpow1 // ih 1:ltrW // mulrC.
qed.

lemma rpow_int x n : 0%r <= x => x^(n%r) = x^n.
proof.
move=> ge0x; case: (lezWP 0 n)=> [/rpow_nat ->|_] //.
move=> le0n; rewrite -(opprK n%r) rpowN // -fromintN.
by rewrite rpow_nat // ?oppz_ge0 // exprN invrK.
qed.

(* -------------------------------------------------------------------- *)
lemma rpowe_gt0 (x : real): 0%r < e^x.
proof. by rewrite rpoweE exp_gt0. qed.

lemma rpowe_ge0 (x : real): 0%r <= e^x.
proof. by rewrite rpoweE ltrW ?exp_gt0. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt rpoweM (x y : real): e^(x * y) = (e^x)^y.
proof. by rewrite rpowM // e_gt0. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt rpow_mono (x y n : real):
     0%r < n => 0%r <= x => 0%r <= y
  => (x^n <= y^n) <=> (x <= y).
proof.
move=> gt0_n /ler_eqVlt [<-|lt0_x].
+ by rewrite rpow0r gtr_eqF // b2r0 => ^h ->/=; apply/rpow_ge0.
move/ler_eqVlt => [<-|lt0_y].
+ by rewrite rpow0r gtr_eqF // b2r0 !lerNgt iff_negb rpow_gt0.
by rewrite !rpowE // exp_mono ler_pmul2l // ln_mono.
qed.

lemma nosmt rpow_hmono (x y n : real):
  0%r <= n => 0%r <= x <= y => x ^ n <= y ^ n.
proof.
rewrite ler_eqVlt=> -[<-|gt0n]; first by rewrite !rpow0 lerr.
by case=> ge0_x le_xy; rewrite rpow_mono // (ler_trans x).
qed.

lemma nosmt rexpr_hmono (x n m : real) :
  1%r <= x => 0%r <= n <= m => x^n <= x^m.
proof.
move=> ge1x [ge0n lenm]; have ge0m: 0%r <= m by apply/(ler_trans n).
rewrite !rpowE 1,2:(ltr_le_trans 1%r) // exp_mono.
by apply/ler_wpmul2r=> //; apply/ln_ge0.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt le1Dx_rpowe (x : real): 0%r <= x => 1%r+x <= e^x.
proof. by rewrite rpoweE; apply/le1Dx_exp. qed.

(* -------------------------------------------------------------------- *)
require import StdBigop.
(*---*) import Bigreal BRA BRM.

lemma exp_sum (P : 'a -> bool) (F : 'a -> real) s:
  exp (BRA.big P F s) = BRM.big P (fun a => exp (F a)) s.
proof.
elim: s => [|x s ih]; rewrite !(big_nil, big_cons) ?exp0 //.
by case: (P x)=> // Px; rewrite expD ih.
qed.

lemma rpowe_sum (P : 'a -> bool) (F : 'a -> real) s:
  e^(BRA.big P F s) = BRM.big P (fun a => e^(F a)) s.
proof. by rewrite rpoweE exp_sum; apply/eq_bigr=> x _ /=; rewrite rpoweE. qed.

(* -------------------------------------------------------------------- *)
abbrev sqrt (x : real) = x ^ (inv 2%r).

lemma sqrtE x : sqrt x = if x <= 0%r then 0%r else exp (ln x / 2%r).
proof. by rewrite /(^); case: (_ <= 0%r) => //=; rewrite invr_eq0. qed.

lemma ge0_sqrt x : 0%r <= sqrt x.
proof.
by rewrite sqrtE -rpoweE; case: (_ <= 0%r) => //=; apply/rpow_ge0.
qed.

lemma sqrt_gt0 (x : real): 0%r < x => 0%r < sqrt x.
proof. by apply/rpow_gt0. qed.

lemma ge1_sqrt x: 1%r <= x => 1%r <= sqrt x.
proof.
by move=> ge1_x; rewrite -{1}(rpow1r (1%r/2%r)) rpow_hmono /#.
qed.

lemma sqrt0 : sqrt 0%r = 0%r.
proof. by rewrite rpow0r invr_eq0. qed.

lemma sqrtM (x y : real) : 0%r <= x => 0%r <= y =>
  sqrt (x * y) = sqrt x * sqrt y.
proof.
rewrite !ler_eqVlt => -[<-|lt0_x] [<-|lt0_y];
  by rewrite ?(sqrt0, mulr0, mul0r) // rpowMr.
qed.

lemma sqrt_mono (x y : real): 0%r <= x => 0%r <= y =>
  (sqrt x <= sqrt y) <=> (x <= y).
proof. by move=> ge0_x ge0_y; rewrite rpow_mono // invr_gt0. qed.

lemma sqrtsq_ge0 (x : real) : 0%r <= x => sqrt (x ^ 2) = x.
proof.
case/ler_eqVlt => [<-|lt0_x]; first by rewrite expr0z sqrt0.
by rewrite -rpow_int 1:ltrW // -rpowM // divff // rpow1.
qed.

lemma sqrtsq (x : real) : sqrt (x ^ 2) = `|x|.
proof.
case: (0%r <= x) => [^/sqrtsq_ge0 -> /ger0_norm ->//|/ltrNge lt0_x].
rewrite -{1}(opprK x) sqrrN sqrtsq_ge0 1:2!(oppr_ge0, ltrW) //.
by rewrite ltr0_norm.
qed.

lemma sqsqrt x : 0%r <= x => (sqrt x) ^ 2 = x.
proof.
move=> ge0_x; rewrite -rpow_int 1:&ge0_sqrt; move: ge0_x.
rewrite ler_eqVlt => -[<-|gt0_x]; first by rewrite sqrt0 rpow0r.
by rewrite -rpowM // mulVf // rpow1.
qed.

(* -------------------------------------------------------------------- *)
op D2 (a b c : real) = exp b 2 - 4%r * a * c.

lemma poly2_canon (a b c : real) (x : real) : a <> 0%r =>
  let A = -b / (2%r * a) in
  let B = - (D2 a b c / (4%r * a)) in
  a * exp x 2 + b * x + c = a * exp (x - A) 2 + B.
proof.
move=> nz_a AE BE; rewrite /AE /BE /D2 #field;
  by rewrite ?mulf_eq0 nz_a.
qed.

lemma poly2_solve (a b c : real) (x : real) :
     a <> 0%r => 0%r <= D2 a b c
  => (   a * exp x 2 + b * x + c = 0%r
     <=> exists (z : real), exp z 2 = D2 a b c /\ x = (-b + z) / (2%r * a)).
proof.
move=> nz_a ge0_D2; split; last first.
+ case=> z [] z2E ->; rewrite #field ?mulf_eq0 //.
  by rewrite z2E /D2 #ring.
have /= -> := poly2_canon a b c x nz_a; rewrite subr_eq0.
rewrite -(mulr1 (D2 a b c / (4%r * a))) (mulrC a) -eqf_div // divr1.
move=> h; exists ((x + b / (2%r * a)) * (2%r * a)); split.
+ by rewrite expfM h #field ?mulf_eq0.
+ by rewrite #field mulf_eq0.
qed.

lemma poly2_same_sign (a b c : real) : a <> 0%r =>
     (forall (x : real), 0%r <= a * (a * exp x 2 + b * x + c))
  => D2 a b c <= 0%r.
proof.
move=> nz_a; pose z := -b / (2%r * a); move/(_ z).
have /= := poly2_canon a b c z nz_a => ->.
rewrite /z addNr expr0z b2r0 /= mulrN oppr_ge0 mulrCA.
by rewrite invfM (mulrCA a) divff // mulr1 pmulr_lle0 ?invr_gt0.
qed.

(* -------------------------------------------------------------------- *)
abstract theory CauchySchwarz.

(* -------------------------------------------------------------------- *)
type t.

clone FinType with type t <- t.

abbrev dim = FinType.card.

lemma ge0_dim : 0 <= dim.
proof. by apply/ltzW/FinType.card_gt0. qed.

(* -------------------------------------------------------------------- *)
type vector = [Vector of (t -> real)].

op "_.[_]" v i = with v = Vector v => v i.

lemma eqvP v1 v2 : (v1 = v2) <=> (forall i, v1.[i] = v2.[i]).
proof.
by split=> [->//|]; case: v1 v2 => [v1] [v2] /= h; apply/fun_ext.
qed.

op zerov  = Vector (fun _ => 0%r).
op ( +  ) = fun v1 v2 => Vector (fun i => v1.[i] + v2.[i]).
op [ -  ] = fun v => Vector (fun i => - v.[i]).
op ( ** ) = fun z v => Vector (fun i => z * v.[i]).

abbrev ( - ) v1 v2 = v1 + (- v2).

(* -------------------------------------------------------------------- *)
lemma zerovE i : zerov.[i] = 0%r.
proof. by []. qed.

lemma addvE v1 v2 i : (v1 + v2).[i] = v1.[i] + v2.[i].
proof. by []. qed.

lemma oppvE v i : (- v).[i] = - v.[i].
proof. by []. qed.

lemma scalevE a v i : (a ** v).[i] = a * v.[i].
proof. by []. qed.

(* -------------------------------------------------------------------- *)
clone include Ring.ZModule with
  type t     <- vector,
  op   zeror <- zerov,
  op   ( + ) <- ( + ),
  op   [ - ] <- [ - ]
  proof *  remove abbrev (-).

realize add0r.
proof. by move=> v; apply/eqvP=> i; rewrite addvE zerovE. qed.

realize addrC.
proof. by move=> v1 v2; apply/eqvP=> i; rewrite !addvE addrC. qed.

realize addrA.
proof. by move=> v1 v2 v3; apply/eqvP=> i; rewrite !addvE addrA. qed.

realize addNr.
proof. by move=> v; apply/eqvP=> i; rewrite addvE oppvE. qed.

(* -------------------------------------------------------------------- *)
lemma scalevA a b v : a ** (b ** v) = a * b ** v.
proof. by apply/eqvP=> i; rewrite !scalevE mulrA. qed.

lemma scale1v v : 1%r ** v = v.
proof. by apply/eqvP=> i; rewrite !scalevE mul1r. qed.

lemma scalevDr a v1 v2 : a ** (v1 + v2) = a ** v1 + a ** v2.
proof. by apply/eqvP=> i; rewrite !(scalevE, addvE) mulrDr. qed.

lemma scalevDl (a b : real) v : (a + b) ** v = a ** v + b ** v.
proof. by apply/eqvP=> i; rewrite !(scalevE, addvE) mulrDl. qed.

lemma scale0v v : 0%r ** v = zerov.
proof. by apply/eqvP=> i; rewrite scalevE mul0r. qed.

lemma scaler0 a : a ** zerov = zerov.
proof. by apply/eqvP=> i; rewrite scalevE. qed.

lemma scaleNv (a : real) v : (- a) ** v = - (a ** v).
proof. by apply/eqvP=> i; rewrite !(scalevE, oppvE) mulNr. qed.

lemma scaleN1v v : (- 1%r) ** v = - v.
proof. by rewrite scaleNv scale1v. qed.

lemma scalevN a v : a ** (- v) = - (a ** v).
proof. by apply/eqvP=> i; rewrite !(scalevE, oppvE) mulrN. qed.

lemma scalerBl (a b : real) v : (a - b) ** v = a ** v - b ** v.
proof. by rewrite scalevDl scaleNv. qed.

lemma scalerBr a u v : a ** (u - v) = a ** u - a ** v.
proof. by rewrite scalevDr scalevN. qed.

(* -------------------------------------------------------------------- *)
op dotp : vector -> vector -> real.

axiom ge0_dotp x : 0%r <= dotp x x.

axiom dotp_def x : dotp x x = 0%r => x = zerov.

axiom dotpC x y : dotp x y = dotp y x.

axiom dotpDl x1 x2 y : dotp (x1 + x2) y = dotp x1 y + dotp x2 y.

axiom dotpZl (c : real) x y : dotp (c ** x) y = c * dotp x y.

lemma dotpDr x y1 y2 : dotp x (y1 + y2) = dotp x y1 + dotp x y2.
proof. by rewrite dotpC dotpDl !(@dotpC x). qed.

lemma dotpZr c x y : dotp x (c ** y) = c * dotp x y.
proof. by rewrite dotpC dotpZl dotpC. qed.

lemma dotpNl x y : dotp (- x) y = - dotp x y.
proof. by rewrite -scaleN1v dotpZl mulN1r. qed.

lemma dotpNr x y : dotp x (- y) = - (dotp x y).
proof. by rewrite dotpC dotpNl dotpC. qed.

lemma dotpBl x1 x2 y : dotp (x1 - x2) y = dotp x1 y - dotp x2 y.
proof. by rewrite dotpDl dotpNl. qed.

lemma dotpBr x y1 y2 : dotp x (y1 - y2) = dotp x y1 - dotp x y2.
proof. by rewrite dotpDr dotpNr. qed.

lemma dotpv0 x : dotp x zerov = 0%r.
proof. by rewrite -(@subrr zerov) dotpBr. qed.

lemma dotp0v x : dotp zerov x = 0%r.
proof. by rewrite dotpC dotpv0. qed.

(* -------------------------------------------------------------------- *)
abbrev norm x = sqrt (dotp x x).

lemma normv0 : norm zerov = 0%r.
proof. by rewrite dotpv0 sqrt0. qed.

lemma normvZ a v : norm (a ** v) = `|a| * norm v.
proof.
rewrite !(dotpZl, dotpZr) mulrA sqrtM ?ge0_dotp.
+ by rewrite -expr2 ge0_sqr.
+ by rewrite -expr2 sqrtsq.
qed.

lemma ge0_normv x : 0%r <= norm x.
proof. by apply/ge0_sqrt. qed.

lemma sqnormv x : (norm x)^2 = dotp x x.
proof. by rewrite sqsqrt // ge0_dotp. qed.

lemma sqnormvD x y :
  (norm (x + y))^2 = (norm x)^2 + 2%r * dotp x y + (norm y)^2.
proof. by rewrite !sqnormv !(dotpDl, dotpDr) (@dotpC y x) #ring. qed.

(* -------------------------------------------------------------------- *)
lemma CZ x y : dotp x y <= norm x * norm y.
proof.
case: (dotp x y < 0%r) => ge0_xy.
+ by apply/ltrW/(ltr_le_trans _ _ _ ge0_xy)/mulr_ge0; apply: ge0_normv.
case: (y = zerov) => [->|nz_y]; first by rewrite normv0 dotpv0 mulr0.
pose P := fun t => (norm (x + t ** y))^2.
pose a := (norm y)^2; pose b := 2%r * dotp x y; pose c := (norm x)^2.
have PE : forall t, P t = a * exp t 2 + b * t + c.
+ move=> t @/P @/a @/b @/c; rewrite sqnormvD dotpZr mulrA #ring.
rewrite normvZ expfM mulNr addrC subr_eq0; congr.
by rewrite -normrX_nat // ger0_norm // ge0_sqr.
have nz_a : a <> 0%r by rewrite /a sqnormv; apply/negP => /dotp_def.
have ge0_aP : forall t, 0%r <= a * P t.
+ move=> t @/P; rewrite mulr_ge0.
* by rewrite /a ge0_sqr. * by apply/ge0_sqr.
have @/D2 := poly2_same_sign a b c nz_a _.
+ by move=> t; have := ge0_aP t; rewrite PE.
have ->: 4%r = exp 2%r 2 by rewrite expr2.
rewrite subr_le0 /a /c -!expfM /b mulrAC.
have ge0_lhs : 0%r <= 2%r * dotp x y by rewrite mulr_ge0 // lerNgt.
have ge0_rhs : 0%r <= 2%r * norm x * norm y.
+ by rewrite !mulr_ge0 // ge0_normv.
by rewrite -!rpow_int // rpow_mono // -!mulrA ler_pmul2l.
qed.

end CauchySchwarz.
