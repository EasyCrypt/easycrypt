(* -------------------------------------------------------------------- *)
require import Fun Int IntExtra Real RealExtra StdRing StdOrder.
(*---*) import RField RealOrder.

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

axiom nosmt le1Dx_exp (x : real): 0%r <= x => 1%r+x <= exp x.

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

lemma nosmt exp_neq0 x : exp x <> 0%r.
proof. by have := (exp_gt0 x); rewrite ltr_neqAle eq_sym => []. qed.

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
rewrite ler_eqVlt => [<-|/rpow_gt0 /(_ n) /ltrW] //.
by rewrite rpow0r; case: (n = 0%r).
qed.

(* -------------------------------------------------------------------- *)
lemma rpowN (x n : real) : 0%r <= x => x^(-n) = inv (x ^ n).
proof.
rewrite ler_eqVlt=> [<-|]; first rewrite !rpow0r oppr_eq0.
  by case: (n = 0%r); rewrite !(invr0, invr1).
by move=> gt0x; rewrite !rpowE // mulNr expN.
qed.

lemma rpowD (x n m : real) : 0%r < x => x^(n + m) = x^n * x^m.
proof. by move=> gt0x; rewrite !rpowE // mulrDl expD. qed.

lemma rpowB (x n m : real) : 0%r < x => x^(n - m) = x^n / x^m.
proof. by move=> gt0x; rewrite subrE divrE !(rpowN, rpowD) // ltrW. qed.

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
proof. by move=> gt0x gt0y; rewrite !divrE rpowMr ?invr_gt0 // rpowVr. qed.

lemma rpow_nat x n : 0 <= n => 0%r <= x => x^(n%r) = x^n.
proof.
elim: n=> [|n ge0n ih] ge0x; first by rewrite Power_0 -FromInt.One rpow0.
rewrite Power_s /(>=) // FromInt.Add; move: ge0x.
rewrite ler_eqVlt=> [<-|]; first rewrite (mul0r 0%r).
  by rewrite rpow0r -FromInt.Add from_intMeq addz1_neq0.
by move=> gt0x; rewrite rpowD // rpow1 // mulrC ih 1:ltrW.
qed.

lemma rpow_int x n : 0%r <= x => x^(n%r) = x^n.
proof.
move=> ge0x; case: (lezWP 0 n)=> [/rpow_nat ->|_] //.
move=> le0n; rewrite -(opprK n%r) rpowN // -FromInt.Neg.
by rewrite rpow_nat // ?oppz_ge0 // pow_inv invrK.
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
     0%r < n => 0%r < x => 0%r < y
  => (x^n <= y^n) <=> (x <= y).
proof.
move=> gt0n gt0x gt0y; rewrite !rpowE //.
by rewrite exp_mono ler_pmul2l // ln_mono.
qed.

lemma nosmt rpow_hmono (x y n : real):
  0%r <= n => 0%r <= x <= y => x ^ n <= y ^ n.
proof.
rewrite ler_eqVlt=> [<-|gt0n]; first by rewrite !rpow0 lerr.
case; rewrite ler_eqVlt=> [<-|gt0x] ge0y.
  move: gt0n; rewrite rpow0r ltr_neqAle eq_sym.
  by case=> [-> _]; apply/rpow_ge0.
by rewrite rpow_mono //; apply/(ltr_le_trans x).
qed.

lemma nosmt rpowr_hmono (x n m : real) :
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
