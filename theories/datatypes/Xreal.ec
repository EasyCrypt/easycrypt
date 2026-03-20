require import AllCore RealSeries List Distr StdBigop DBool DInterval.  
require import StdOrder.
require Subtype Bigop.
import Bigreal Bigint RealOrder.

(* -------------------------------------------------------------------- *)
(* Definition of R+                                                     *)

abstract theory MonoidD.
  clone include Monoid 
    rename "idm" as "zero"
    rename "iteropE" as "iteraddE". 

  op ( * ) : t -> t -> t.

  clone export Monoid as MulMonoid with 
    type t <- t,
    op ( + ) <- ( * )
    rename "idm" as "one"
    rename "add0m" as "mul1m"
    rename "addm0" as "mulm1"
    rename "add" as "mul"
    rename "iteropE" as "itermulE". 

  axiom one_neq0 : one <> zero.
  axiom mulmDl    : left_distributive ( * ) (+).

  lemma mulmACA: interchange ( * ) ( * ).
  proof. by move=> x y z t; rewrite -!mulmA (mulmCA y). qed.

  lemma mulmDr: right_distributive ( * ) (+).
  proof. by move=> x y z; rewrite mulmC mulmDl !(@mulmC _ x). qed.

  lemma addm0_simpl x : x + zero = x by apply addm0.
  lemma add0m_simpl x : zero + x = x by apply add0m.
  lemma mul1m_simpl x : one * x = x by apply mul1m.
  lemma mulm1_simpl x : x * one = x by apply mulm1.

  hint simplify addm0_simpl, add0m_simpl, mul1m_simpl, mulm1_simpl.

end MonoidD.

abstract theory MonoidDI.
  clone include MonoidD.
 
  axiom addmI: right_injective (+).

  lemma addIm: left_injective (+).
  proof. by move=> x y z; rewrite !(addmC _ x) => /addmI. qed.

  lemma mul0m: left_zero zero ( * ).
  proof. by move=> x; apply: (@addIm (one * x)); rewrite -mulmDl !add0m mul1m. qed.

  lemma mulm0: right_zero zero ( * ).
  proof. by move=> x; rewrite mulmC mul0m. qed.

  lemma mul0m_simpl x : zero * x = zero by apply mul0m.
  lemma mulm0_simpl x : x * zero = zero by apply mulm0.
  hint simplify mul0m_simpl, mulm0_simpl.

end MonoidDI.

theory Rp.

subtype realp = { x : real | 0.0 <= x }
  rename "of_real", "to_real".
realize inhabited by exists 0%r.

abbrev (%r) = to_real.
abbrev (%rp) = of_reald.

lemma of_realKd_ge0 (x : real): 0%r <= x => x%rp%r = x.
proof. smt(of_realdK to_realP). qed.

lemma of_reald_pinj (x y:real):
  0%r <= x => 0%r <= y => x%rp = y%rp => x = y.
proof.
move=> ge0_x ge0_y.
move: (of_realP x); rewrite ge0_x=> /= - [] xp [] xpP <-.
move: (of_realP y); rewrite ge0_y=> /= - [] yp [] ypP <-.
by rewrite !to_realKd.
qed.

theory IntNotation.
  abbrev (%rp) (n:int) = n%r%rp.
end IntNotation. export IntNotation.

axiom witness_0 : witness = 0%rp.

lemma of_real_neg x : x < 0.0 =>  x%rp = 0%rp.
proof. smt(to_realK to_real_of_reald witness_0). qed.

lemma of_real_le0 x : x <= 0%r => x%rp = 0%rp.
proof. by rewrite ler_eqVlt; case => [->// | /of_real_neg]. qed.

lemma to_realK_simpl (x:realp) : x%r%rp = x by apply: to_realKd.
hint simplify to_realK_simpl, of_realdK.

lemma to_realP_simpl x : (0.0 <= x%r) = true by rewrite to_realP. 
hint simplify to_realP_simpl.

op ( + ) (x y : realp) = (x%r + y%r)%rp.

op ( * ) (x y : realp) = (x%r * y%r)%rp.

op inv (x : realp) = (inv x%r)%rp.

abbrev (/) (x y : realp) : realp = x * inv y.

abbrev (<=) (x y : realp) = x%r <= y%r.
abbrev (<) (x y : realp)  = x%r < y%r.

lemma addrpA: associative Rp.(+).
proof.
move=> x y z; rewrite /(+).
congr; rewrite !of_realKd_ge0 ?addr_ge0 //.
exact: RField.addrA.
qed.

lemma addrpC: commutative Rp.(+).
proof.
move=> x y; rewrite /(+).
by congr; exact: RField.addrC.
qed.

lemma add0rp: left_id 0%rp (+).
proof. done. qed.

lemma mulrpA: associative Rp.( * ).
proof.
move=> x y z; rewrite /( * ).
congr; rewrite !of_realKd_ge0 ?mulr_ge0 //.
exact: RField.mulrA.
qed.

lemma mulrpC: commutative Rp.( * ).
proof.
move=> x y; rewrite /( * ).
by congr; exact: RField.mulrC.
qed.

lemma mul1rp: left_id 1%rp Rp.( * ).
proof. done. qed.

lemma one_neq0_rp: 1%rp <> 0%rp.
proof. by rewrite -negP=> eq_10; move: (of_reald_pinj 1%r 0%r _ _). qed.

lemma mulrpDl: left_distributive Rp.( * ) Rp.(+).
proof.
move=> x y z; rewrite /(+) /( * ).
congr; rewrite !of_realKd_ge0 ?(addr_ge0, mulr_ge0) //.
by rewrite RField.mulrDl.
qed.

lemma addrpI: right_injective Rp.(+).
proof.
move=> x y y'; rewrite /(+)=> /(congr1 to_real).
rewrite !of_realKd_ge0 ?addr_ge0 //.
by move=> /RField.addrI/to_real_inj.
qed.
clone include MonoidDI with
   type t  <- realp,
   op zero <- of_reald 0.0,
   op MulMonoid.one  <- of_reald 1.0,
   op ( + ) <- Rp.( + ),
   op ( * ) <- Rp.( * ),
   lemma Axioms.addmA <- addrpA,
   lemma Axioms.addmC <- addrpC,
   lemma Axioms.add0m <- add0rp,
   lemma MulMonoid.Axioms.mulmA <- mulrpA,
   lemma MulMonoid.Axioms.mulmC <- mulrpC,
   lemma MulMonoid.Axioms.mul1m <- mul1rp,
   lemma one_neq0 <- one_neq0_rp,
   lemma mulmDl <- mulrpDl,
   lemma addmI <- addrpI
proof *.

lemma to_realD (x y:realp) : (x + y)%r = x%r + y%r.
proof. smt (of_realdK to_realP). qed.

lemma to_realM (x y:realp) : (x * y)%r = x%r * y%r.
proof. smt (of_realdK to_realP). qed.

lemma to_realI x : (inv x)%r = inv x%r.
proof. smt (of_realdK to_realP Real.invr0). qed.

hint simplify to_realD, to_realM, to_realI.

lemma of_realD x y : 0.0 <= x => 0.0 <= y => 
   (x + y)%rp = x%rp + y%rp.
proof. smt (of_realdK to_realP). qed.

lemma of_realM x y : 0.0 <= x => 0.0 <= y => 
   (x * y)%rp = x%rp * y%rp.
proof. smt (of_realdK to_realP). qed.

lemma of_realI (x:real) : (inv x)%rp = inv x%rp.
proof. smt (of_realdK to_realP  of_real_neg divr0). qed.
hint simplify of_realI.

op (%pos) (x:real) = if 0.0 <= x then x else 0.0.

lemma to_pos_pos (x:real) : 0.0 <= x => x%pos = x.
proof. by rewrite /(%pos) => ->. qed.
hint simplify to_pos_pos @10.

lemma le_pos (x y : real) : x <= y => x%pos <= y%pos
by smt(). 

lemma inv_pos x : inv x%pos = (inv x)%pos
by smt(divr0).

lemma to_real_of_real (x:real) : x%rp%r = x%pos.
proof. by rewrite to_real_of_reald witness_0. qed.
hint simplify to_real_of_real.

lemma to_pos_mu ['a] (d : 'a distr) (e: 'a -> bool) : 
  (mu d e)%pos = mu d e.
proof. by rewrite /(%pos) ge0_mu. qed.

hint simplify to_pos_mu.

end Rp.
export Rp.

(* -------------------------------------------------------------------- *)
(* Definition of R+oo *)

theory Rpbar.

type xreal = [rp of realp | oo].

abbrev (%xr) = rp.

theory RealNotation.
abbrev (%xr) (x:real) = x%rp%xr.
end RealNotation. export RealNotation.

theory IntNotation.
abbrev (%xr) (i:int)  = i%r%xr.
end IntNotation. export IntNotation.

theory BoolNotation.
abbrev (%xr) (b:bool)  = (b2r b)%xr.
end BoolNotation. export BoolNotation.

(* -------------------------------------------------------------------- *)
abbrev ('0) = 0.0%xr.
abbrev ('1) = 1.0%xr.

op xadd (x y : xreal) =
  with x = rp x, y = rp y => (x + y)%xr
  with x = rp _, y = oo  => oo
  with x = oo , y = rp _ => oo
  with x = oo , y = oo  => oo.

op xmul (x y : xreal) =
  with x = rp x, y = rp y => (x * y)%xr
  with x = rp _, y = oo  => oo
  with x = oo , y = rp _ => oo
  with x = oo , y = oo  => oo.

op xinv (x : xreal) = 
  with x = rp x => (inv x)%xr
  with x = oo  => oo.  (* Does this make sense *)

abbrev ( + ) = xadd.
abbrev ( * ) = xmul.

abbrev (/) (x y : xreal) : xreal = x * xinv y.

op ( ** ) c x =
  if c = 0.0%rp then '0 else c%xr * x. 

theory Notation.
abbrev ( ** ) (x:real) (z:xreal) = x%rp ** z.
end Notation. export Notation.

op to_real (x:xreal) = 
  with x = rp y => y%r
  with x = oo => 0.0.

op is_real (x:xreal) = 
  with x = rp _  => true
  with x = oo => false.

op is_oo (x:xreal) = 
  with x = rp _ => false
  with x = oo => true.

op xle (x y : xreal) = 
  with x = rp x, y = rp y => x <= y
  with x = rp _, y = oo  => true 
  with x = oo , y = rp _ => false
  with x = oo , y = oo  => true.

op xlt (x y : xreal) = 
  with x = rp x, y = rp y => x < y
  with x = rp _, y = oo  => true 
  with x = oo , y = rp _ => false
  with x = oo , y = oo  => false.

abbrev (<=) = xle.
abbrev (<) = xlt.

(* -------------------------------------------------------------- *)
clone include MonoidD with 
  type t <- xreal,
  op zero <- 0%xr,
  op MulMonoid.one  <- 1%xr,
  op ( + ) <- xadd,
  op ( * ) <- xmul
  proof *.
realize Axioms.addmA by move=> [x|] [y|] [z|] //=; apply Rp.addmA. 
realize Axioms.addmC by move=> [x|] [y|] //=; apply Rp.addmC.
realize Axioms.add0m by move=> [x|] //=; apply Rp.add0m.
realize MulMonoid.Axioms.mulmA by move=> [x|] [y|] [z|] //=; apply Rp.MulMonoid.mulmA.
realize MulMonoid.Axioms.mulmC by move=> [x|] [y|] //=; apply Rp.MulMonoid.mulmC.
realize MulMonoid.Axioms.mul1m by move=> [x|] //=; apply Rp.MulMonoid.mul0m.
realize one_neq0 by apply/negP => /(congr1 to_real).
realize mulmDl by move=> [x|] [y|] [z|] //=; apply Rp.mulrpDl.

(* -------------------------------------------------------------- *)
lemma xaddxoo x : x + oo = oo.
proof. by case: x. qed.

lemma xaddoox x : oo + x = oo.
proof. by case: x. qed.

lemma xmulxoo x : x * oo = oo.
proof. by case: x. qed.

lemma xmuloox x : oo * x = oo.
proof. by case: x. qed.

hint simplify xaddxoo, xaddoox, xmulxoo, xmuloox.

(* -------------------------------------------------------------- *)

lemma smul0m x : 0%r ** x = '0.
proof. by rewrite /( ** ). qed.

lemma smul1m x : 1%r ** x = x.
proof. by rewrite /( ** ) one_neq0. qed.

hint simplify smul0m, smul1m.

lemma smulmDr x y z: x ** (y + z) = x ** y + x ** z. 
proof. by rewrite /( ** ); case: (x = of_reald 0%r) => //= ?; apply mulmDr. qed.

lemma smulmCA d x y : d ** (rp x * y) = rp x * (d ** y).
proof. by rewrite /( ** ); case: (d = of_reald 0.0) => //=; rewrite mulmCA. qed.

lemma smulmA d x y : d ** (x * rp y) = (d ** x) * rp y.
proof. by rewrite /( ** ); case: (d = of_reald 0.0) => //=;rewrite mulmA. qed.

lemma smulmAC d x y : d ** (x * rp y) = rp y * (d ** x) .
proof. by rewrite mulmC smulmCA. qed.

lemma smulrp x y : x ** rp y =  rp (x * y).
proof. by rewrite /( ** ); case: (x = of_reald 0.0). qed.
hint simplify smulrp.

(* -------------------------------------------------------------- *)

lemma xle0x x : 0%xr <= x.
proof. by case: x. qed.

lemma xlexx x : x <= x.
proof. by case: x. qed.

lemma xlexoo x : x <= oo.
proof. by case: x. qed.

lemma xlexx_simpl x y : x = y => x <= y = true.
proof. by move=> ->; rewrite xlexx. qed.

lemma xlexoo_simpl x : x <= oo = true.
proof. by case: x. qed.

hint simplify xlexx_simpl, xlexoo_simpl.

lemma xltxx x : !x < x.
proof. by case: x. qed.

lemma xltxx_simpl x y : x = y => x < y = false.
proof. by move=> ->; rewrite xltxx. qed.

hint simplify xltxx_simpl.

lemma xle_trans (y x z : xreal) : x <= y => y <= z => x <= z.
proof.
  case: z => // z; case: y => // y; case: x => //=; smt(@Rp).
qed.

lemma xle_add_r x y : x <= x + y.
proof. case: x y => [x|] [y|] //=; smt(@Rp). qed.

lemma xle_add_l x y : x <= y + x.
proof. rewrite addmC xle_add_r. qed.

lemma xler_add2r (x:realp) (y z : xreal) : y + x%xr <= z + x%xr <=> y <= z.
proof. case: z => // z; case: y => //= y; smt(@Rp). qed.

lemma xler_add2l (x:realp) (y z : xreal) : rp x + y <= x%xr + z <=> y <= z.
proof. rewrite !(addmC (rp x)); apply xler_add2r. qed.

lemma xler_addr (x y z : xreal) : y <= z => y + x <= z + x.
proof. case x => // x /xler_add2r; apply. qed.

lemma xler_addl (x y z : xreal) : y <= z => x + y <= x + z.
proof. case x => // x /xler_add2l; apply. qed.

lemma xler_add (x y z t : xreal) : x <= y => z <= t => x + z <= y + t.
proof. by move=> /(xler_addr z) h1 /(xler_addl y); apply xle_trans. qed.

lemma xler_pmul2l (x:realp) : 0%rp < x => 
  forall (y z : xreal),
  rp x * y <= rp x * z <=> y <= z.
proof.
rewrite (of_realdK 0%r) //.
move=> hx y z; case: z => // z; case: y => // y.
by rewrite /= -!to_realM !to_realM ler_pmul2l.
qed.

lemma xler_wpmul2l (x : realp) (y z : xreal) :
  y <= z => x%xr * y <= x%xr * z.
proof. case: z => // z; case: y => // y; smt(to_realP). qed.

lemma xler_pmul2r (x:realp) : 0%rp < x => 
  forall (y z : xreal),
  y * rp x <= z * rp x <=> y <= z.
proof.
rewrite (of_realdK 0%r) //.
move=> hx y z; case: z => // z; case: y => // y.
by rewrite /= -!to_realM !to_realM ler_pmul2r.
qed.

lemma xler_wpmul2r (x : realp) (y z : xreal) :
  y <= z => y * x%xr <= z * x%xr.
proof. case: z => // z; case: y => // y; smt(to_realP). qed.

lemma xler_mulr (x y z : xreal) : y <= z => y * x <= z * x.
proof. case x => // x /xler_wpmul2r; apply. qed.

lemma xler_mull (x y z : xreal) : y <= z => x * y <= x * z.
proof. case x => // x /xler_wpmul2l; apply. qed.

lemma xler_mul (x y z t : xreal) : x <= y => z <= t => x * z <= y * t.
proof. by move=> /(xler_mulr z) h1 /(xler_mull y); apply xle_trans. qed.

lemma xler_md x y c : ((0%r < c) => x <= y) => c ** x <= c ** y.
proof.
  move=> h; rewrite /( **).
  case: (0%r < c ) => hc.
  + have -> /=: (c%rp <> 0%rp) by smt(to_realP of_realdK to_realK_simpl).
    by apply/xler_mull/h.
  by have -> : (c%rp = 0%rp) by smt(of_real_neg).
qed.

(* -------------------------------------------------------------- *)
lemma md_realP (c : real) (x : xreal) :
  is_real (c ** x) <=> c <= 0%r \/ x <> oo.
proof.
case: x => //= @/( ** ); case: (c <= 0%r) => /=.
- by move/of_real_le0 => ->.
- move/ltrNge => gt0_c; rewrite -(inj_eq _ to_real_inj) /=.
  by rewrite to_pos_pos 1:&ltrW // gtr_eqF.
qed.

lemma md_eqinfP (c : real) (x : xreal) :
  c ** x = oo <=> 0%r < c /\ x = oo.
proof.
have := md_realP c x; case: (c ** x) => //=.
- by rewrite negb_and ltrNge.
- by rewrite negb_or ltrNge.
qed.

lemma to_real_md (c : real) (x : xreal) :
  to_real (c ** x) = c%pos * to_real x.
proof. by case: x => //= @/( ** ); case: (c%rp = 0%rp). qed.

lemma is_real_le x y : x <= y => is_real y => is_real x.
proof. by case: x y => [x|] [y|]. qed.

lemma is_realZ p x : is_real (rp p * x) = is_real x.
proof. by case: x. qed.

lemma is_realD x y : is_real (x + y) <=> is_real x /\ is_real y.
proof. by case: x y => [x|] [y|]. qed.

lemma is_realM x y : is_real (x * y) <=> is_real x /\ is_real y.
proof. by case: x y => [x|] [y|]. qed.

lemma to_realP x : 0.0 <= to_real x.
proof. case: x => //=; apply to_realP. qed.

lemma to_realD (x y : xreal) : 
  is_real x => is_real y =>
  to_real (x + y) = to_real x + to_real y.
proof. by case: x y => [x|] [y|]. qed.

lemma to_realM (x y : xreal) : 
  to_real (x * y) = to_real x * to_real y.
proof. by case: x y => [x|] [y|]. qed.

end Rpbar. export Rpbar.

theory Lift.

  abbrev ( + ) (f1 f2 : 'a -> xreal) = 
    fun (x : 'a) => f1 x + f2 x.

  abbrev ( * ) (f1 f2 : 'a -> xreal) = 
    fun (x : 'a) => f1 x * f2 x.

  abbrev ( ** ) (d : 'a distr) (f : 'a -> xreal) =
    fun (x : 'a) => of_reald (mu1 d x) ** f x.

  op is_real ['a] (f : 'a -> xreal) = 
    forall x, is_real (f x).

  op to_real ['a] (f : 'a -> xreal) = 
    fun x => to_real (f x).

  lemma is_realPn ['a] (f : 'a -> xreal) :
    !is_real f <=> exists x, f x = oo.
  proof.
  split.
  - by case/negb_forall=> /= y fyE; exists y; case: (f y) fyE.
  - by case=> x fxE; apply/negP => /(_ x); rewrite fxE.
  qed.

  lemma to_real_mdfun (d : 'a distr) (f : 'a -> xreal) :
    to_real (d ** f) = fun x => mu1 d x * to_real (f x).
  proof. by apply/fun_ext=> x; rewrite /to_real to_real_md. qed.

  lemma eq_is_real ['a] (f g : 'a -> xreal) :
    (forall (x : 'a), f x = g x) => 
    is_real f = is_real g.
  proof. move=> h; congr; apply/fun_ext/h. qed.

  lemma eq_to_real ['a] (f g : 'a -> xreal) : 
    (forall (x : 'a), f x = g x) => 
    to_real f = to_real g.
  proof. move=> h; congr; apply/fun_ext/h. qed.

  lemma eq_md ['a] (d : 'a distr) (f g : 'a -> xreal) :
    (forall (x : 'a), x \in d => f x = g x) => 
    d ** f = d ** g.
  proof. move=> h; apply/fun_ext => x; smt(ge0_mu). qed.

  lemma eq_is_real_md ['a] (d : 'a distr) (f g : 'a -> xreal) :
    (forall (x : 'a), x \in d => f x = g x) => 
    is_real (d ** f) = is_real (d ** g).
  proof. by move=> /eq_md ->. qed.

  lemma eq_to_real_md ['a] (d : 'a distr) (f g : 'a -> xreal) : 
    (forall (x : 'a), x \in d => f x = g x) => 
    to_real (d ** f) = to_real (d ** g).
  proof. by move=> /eq_md ->. qed.
  
  lemma mdDr ['a] : right_distributive Lift.( ** )<:'a> Lift.( + ).
  proof. by move=> d f1 f2; apply fun_ext => x; apply smulmDr. qed.

  lemma mdCA ['a] (d : 'a distr) x f : d ** (fun z => rp x * f z) = fun z => rp x * (d ** f) z.
  proof. by apply fun_ext => z; rewrite smulmCA. qed.

  lemma mdA ['a] (d : 'a distr) f y : d ** (fun z => f z * rp y) = fun z => (d ** f) z * rp y.
  proof. by apply fun_ext => z; rewrite smulmA. qed.

  lemma mdAC ['a] (d : 'a distr) f y : d ** (fun z => f z * rp y) = fun z => rp y * (d ** f) z.
  proof. by apply fun_ext => z; rewrite smulmAC. qed.

  lemma is_real_le (f g : 'a -> xreal) : (forall (x : 'a), f x <= g x) =>
     is_real g => is_real f.
  proof. move=> hfg hg x; apply/(is_real_le _ (g x)); [apply/hfg | apply/hg]. qed.

  lemma is_real_le_md (d:'a distr) (f g : 'a -> xreal) : 
    (forall (x : 'a), x \in d => f x <= g x) =>
    is_real (d ** g) => is_real (d ** f).
  proof. move=> h; apply is_real_le => //= x; apply/xler_md/h. qed.

  lemma is_realZ ['a] c (f : 'a -> xreal) : is_real (fun x => rp c * f x) <=> is_real f.
  proof. by split => h x; have := h x; rewrite is_realZ. qed.

  lemma is_realD ['a] (f1 f2 : 'a -> xreal) :
    is_real (f1 + f2) <=> (is_real f1 /\ is_real f2).
  proof.
    rewrite /is_real; split.
    + by move=> h; split => x; have /is_realD := h x.
    by move=> [h1 h2] x; apply /is_realD; move: (h1 x) (h2 x).
  qed.

  lemma is_realM ['a] (f1 f2 : 'a -> xreal) :
    is_real (f1 * f2) <=> (is_real f1 /\ is_real f2).
  proof.
    rewrite /is_real; split.
    + by move=> h; split => x; have /is_realM := h x.
    by move=> [h1 h2] x; apply /is_realM; move: (h1 x) (h2 x).
  qed.

  lemma is_realMd (f2 f1 : 'a -> xreal) (d : 'a distr) : 
    (forall x, x \in d => is_real (f1 x) = is_real (f2 x)) => 
    is_real (d ** f1) <=> is_real (d ** f2).
  proof.
    move=> h; split => h1 x; have := h1 x; rewrite /( ** );
    case: (of_reald (mu1 d x) = of_reald 0.0) => // ?; rewrite !is_realM h //; smt(mu_bounded).
  qed.

  lemma is_real_rp ['a] (f:'a -> realp) : is_real (fun x => rp (f x)).
  proof. done. qed.

  lemma is_real_sM ['a] (d : 'a  distr) f : 
    is_real (d ** f) <=> forall x, x \in d => is_real (f x).
  proof. split => h x; have := h x; smt (mu_bounded @Rp). qed.

  lemma to_real_rp ['a] (f:'a -> realp) : to_real (fun x => rp (f x)) = fun x => to_real (f x).
  proof. by apply fun_ext. qed.

  lemma to_realZ ['a] c (f: 'a  -> xreal) : 
    to_real (fun x => rp c * f x) = fun x => to_real c * to_real (f x).
  proof. by apply fun_ext => x; rewrite /to_real /= to_realM. qed.

  lemma to_realD ['a] (f g : 'a -> xreal) : 
    is_real f => is_real g =>
    to_real (f + g) = fun x => to_real (f x) + to_real (g x).
  proof.
    rewrite /to_real; move=> h1 h2; apply fun_ext => ?.
    apply to_realD; [apply h1 | apply h2]. 
  qed.

  lemma to_realM ['a] (f g : 'a -> xreal) : 
    to_real (f * g) = fun x => to_real (f x) * to_real (g x).
  proof. rewrite /to_real; apply fun_ext => ?; apply to_realM. qed.

end Lift. export Lift.

clone import Bigop as BXA with
  type t <= xreal,
  op Support.idm <- Rpbar.('0),
  op Support.(+) <- Rpbar.xadd,
  theory Support.Axioms <- Rpbar.Axioms.

lemma is_real_bigRX ['a] (f : 'a -> xreal) l: 
  is_real f => 
  (BRA.big predT (to_real f) l)%xr = big predT f l.
proof.
  move=> hf; elim: l => //= x l hrec.
  rewrite big_cons BRA.big_cons /predT /= -hrec /to_real.
  have := hf x; case: (f x) => //= z.
  by rewrite of_realD // sumr_ge0 /= => a; apply to_realP.
qed.

lemma bigR_to_real ['a] (f : 'a -> real) (l : 'a list) : 
  (forall a, a \in l => 0%r <= f a) =>
   BRA.big predT (to_real (fun a => (f a)%xr)) l = BRA.big predT f l.
proof.
  move=> hpos; apply BRA.eq_big_seq; rewrite /to_real => x /hpos; smt(@Rp).
qed.

lemma bigXR ['a] (f : 'a -> real) (l : 'a list) : 
  (forall a, a \in l => 0%r <= f a) =>
  big predT (fun x => (f x)%xr) l = (BRA.big predT f l)%xr.
proof. by move=> hpos; rewrite -is_real_bigRX 1:// bigR_to_real. qed.

lemma bigXI ['a] (f : 'a -> int) (l : 'a list) : 
  (forall a, a \in l => 0 <= f a) =>
  big predT (fun x => (f x)%xr) l = (BIA.big predT f l)%xr.
proof. by move=> h; rewrite bigXR 1:/# sumr_ofint. qed.

lemma bigiXR (f : int -> real) (m n : int) : 
  (forall i, m <= i < n => 0%r <= f i) =>
  bigi predT (fun x => (f x)%xr) m n = (BRA.bigi predT f m n)%xr.
proof. move=> hpos; apply bigXR => i /mem_range; apply hpos. qed.

lemma bigiXI (f : int -> int) (m n : int) : 
  (forall i, m <= i < n => 0 <= f i) =>
  bigi predT (fun x => (f x)%xr) m n = (BIA.bigi predT f m n)%xr.
proof. move=> hpos; apply bigXI => i /mem_range; apply hpos. qed.

lemma big_oo ['a] (J : 'a list) (f : 'a -> xreal) : 
  (exists (x : 'a), (x \in J) /\ f x = oo) => 
  big predT f J = oo.
proof.
  move=> [x [hj hf]]; rewrite (bigID _ _ (pred1 x)) -big_filter predTI filter_pred1.
  have [n [hn ->]]: exists n, 0 <= n /\ count (pred1 x) J = n + 1.
  + have [+ _]:= has_count (pred1 x) J; rewrite hasP; smt().
  by rewrite nseqS // big_cons /predT hf.
qed.

lemma mulr_sumr ['a] (P : 'a -> bool) (F : 'a -> xreal) (s : 'a list) (x : realp) : 
  x ** (big P F s) = (big P (fun (i : 'a) => x ** F i) s).
proof. apply (big_comp (fun y => x ** y)) => //=; apply smulmDr. qed.


(* -------------------------------------------------------------------- *)

op psuminf ['a] (f : 'a -> xreal) =
  if summable (to_real f) then (sum (to_real f))%xr else oo.

op Ep ['a] (d : 'a distr) (f : 'a -> xreal) =
  let g = d ** f in
  if is_real g then psuminf g else oo.

lemma psuminfZ ['a] (c:realp) (f: 'a -> xreal) :
  is_real f => c <> of_reald 0.0 =>
  psuminf (fun x => rp c * f x) = rp c * psuminf f.
proof.
  move=> hf hc; have heq := summableZ_iff (to_real f) (to_real c) _; 1:smt(@Rp).
  rewrite /psuminf to_realZ -heq. 
  case: (summable (to_real f)) => // hs.
  rewrite sumZ of_realM //.
  by apply ge0_sum => /= x; apply to_realP.
qed.

lemma psumifD (f1 f2 : 'a -> xreal) : 
  is_real f1 => is_real f2 => 
  psuminf (fun x => f1 x + f2 x) = psuminf f1 + psuminf f2.
proof.
  move=> h1 h2; rewrite /psuminf; rewrite to_realD //.
  case: (summable (fun (x : 'a) => to_real (f1 x) + to_real (f2 x))) => hs.
  + have hs1 := summable_le _ (to_real f1) hs _; 1: smt(Rpbar.to_realP).
    have hs2 := summable_le _ (to_real f2) hs _; 1: smt(Rpbar.to_realP).
    by rewrite hs1 hs2 /= sumD // of_realD //; apply ge0_sum => x /=; apply to_realP.
  by case: (summable (to_real f1)); case (summable (to_real f2)) => // hs1 hs2 /=; apply/hs/summableD.
qed.

lemma le_psuminf (f g : 'a -> xreal) :
  (forall (x : 'a), f x <= g x) => 
  is_real g => 
  psuminf f <= psuminf g.
proof.
  rewrite /psuminf => h hg.
  case: (summable (to_real g)) => // hgs.
  have h1 : forall (x : 'a), 0%r <= to_real f x && to_real f x <= to_real g x by smt(Rp.to_realP).
  have -> /= := summable_le_pos (to_real f) (to_real g) hgs h1.
  have:= ler_sum_pos (to_real f) (to_real g) h1 hgs.
  exact: le_pos.
qed.

lemma eq_Ep ['a] (d : 'a distr) (f g : 'a -> xreal) :
  (forall (x : 'a), x \in d => f x = g x) => 
  Ep d f = Ep d g.
proof. by rewrite /Ep /= => /eq_md ->. qed.

lemma le_Ep ['a] (d: 'a distr) (f g : 'a -> xreal) : 
   (forall (x : 'a), x \in d => f x <= g x) => 
  Ep d f <= Ep d g.
proof.
  rewrite /Ep /= => h; case: (is_real (d ** g)) => //.
  move=> h1; rewrite (is_real_le_md _ _ _ h h1) /=.
  apply le_psuminf => //= x; apply/xler_md/h.
qed.

lemma EpC ['a] (d : 'a distr) (c : xreal):
   Ep d (fun (_ : 'a) => c) = (weight d) ** c.
proof.
  case: c => [c | ].
  + rewrite /Ep /= is_real_rp /=. 
    rewrite /psuminf /= to_real_rp /=.
    have -> : (fun (x : 'a) => mu1 d x * to_real c) = (fun (x : 'a) => to_real c * mu1 d x ).
    + by apply fun_ext => x; apply RField.mulrC.
    have /summableZ /= -> /= := summable_mu1 d.
    by rewrite mulmC sumZ /= of_realM // 1: ge0_sum //= weightE; do 3! congr.
  rewrite /Ep /=; case: (weight d = 0%r) => hw.
  + have hx : forall x, mu1 d x = 0%r.
    + move=> x; have := mu_le_weight d (pred1 x); smt(mu_bounded).
    have -> : (fun (x : 'a) => mu1 d x ** oo) = (fun (x:'a) => 0%xr). 
    + by apply fun_ext => x; rewrite hx.
    by rewrite is_real_rp /= /psuminf /= to_real_rp /= summable0 /= sum0 hw.
  rewrite /( **) /=. 
  have -> : !is_real (fun (x : 'a) => if (mu1 d x)%rp = 0%rp then 0%xr else oo).
  + apply/negP => his.
    move/neq0_mu : hw => -[x [hx _]].
    by have := his x; smt(of_realdK to_realP ge0_weight).
  by have -> : (weight d)%rp <> 0%rp by smt(of_realdK to_realP ge0_weight).
qed.

lemma EpZ ['a] (d: 'a distr) (c:realp) (f: 'a -> xreal) :
  c <> of_reald 0.0 => 
  Ep d (fun x => rp c * f x) = rp c * Ep d f.
proof. 
  move=> hc; rewrite /Ep /= (is_realMd f); 1: by move=> x _ /=; rewrite is_realM. 
  case: (is_real (d ** f)) => // hr; rewrite /psuminf.
  rewrite mdCA /= to_realM /=.
  rewrite -summableZ_iff 1:#smt:(@Rp); rewrite /to_real.
  case: (summable (fun (x : 'a) => to_real (of_reald (mu1 d x) ** f x))) => // ?.
  rewrite sumZ /= of_realM // ge0_sum => /= ?; apply to_realP.
qed.

lemma EpsZ ['a] (d: 'a distr) (c:realp) (f: 'a -> xreal) :
  Ep d (fun x => c ** f x) = c ** Ep d f.
proof. 
  rewrite /( ** ); case: (c = of_reald 0%r) => ?; last by apply EpZ.
  by rewrite EpC.
qed.

lemma EpD ['a] (d : 'a distr) (f1 f2 : 'a -> xreal) : 
  Ep d (f1 + f2) = Ep d f1 + Ep d f2.
proof.
  rewrite /Ep /= mdDr.
  have /= := is_realD (d ** f1) (d ** f2).
  case: (is_real (fun x => of_reald (mu1 d x) ** f1 x + of_reald (mu1 d x) ** f2 x)) => h />.
  + by move=> h1 h2; rewrite -psumifD.
  by case: (is_real (d ** f1)) => />.
qed.

lemma Ep_mu (d:'a distr) (p:'a -> bool): 
  Ep d (fun a => (p a)%xr) = (mu d p)%xr.
proof.
  rewrite /Ep /=.
  rewrite (: (fun (x : 'a) => ((mu1 d x)%rp * (b2r (p x))%rp)%xr) = (d ** (fun x => (p x)%xr))) 1://.
  have -> /= : is_real (d ** fun (x : 'a) => (p x)%xr) by apply is_real_sM.
  rewrite /psuminf /to_real /= summable_mu1_wght /= 1:/# muE.
  by congr; apply eq_sum => x /=; case: (p x).
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_fin ['a] J (d : 'a distr) f : 
  uniq J => 
  (forall (x : 'a), mu1 d x <> 0%r => x \in J) =>
  Ep d f = big predT (d ** f) J.
proof.
  move=> hu hJ; rewrite /Ep /=.
  case: (is_real (d ** f)) => his.
  + have hJ' : forall (x : 'a), to_real (d ** f) x <> 0%r => x \in J.
    + by rewrite /to_real /( ** )=> x; case: (of_real (mu1 d x) = of_real 0.0) => //; smt(@Rp).
    by rewrite  /psuminf (summable_fin _ J hJ') /= (sumE_fin _ J hu hJ') is_real_bigRX.
  rewrite big_oo //.
  move/negb_forall: his => /> x hx; exists x.
  move: hx; case _: (mu1 d x ** f x) => //=.
  rewrite /( ** ); case: (of_real (mu1 d x) = of_real 0.0) => //=; smt(@Rp).
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_dnull ['a] f : Ep dnull<:'a> f = Rpbar.('0).
proof. by rewrite (Ep_fin []) // => x; rewrite dnull1E. qed.

(* -------------------------------------------------------------------- *)
lemma Ep_dunit ['a] (x : 'a) f : Ep (dunit x) f = f x.
proof. 
  rewrite (Ep_fin [x]) //; 1: by move=> x'; rewrite dunit1E /#.
  by rewrite big_seq1 /( ** ) /= dunit1E /= one_neq0.
qed.

(* -------------------------------------------------------------------- *)
lemma EP_E ['a] (d : 'a distr) (f : 'a -> xreal) :
     is_real (d ** f)
  => summable (to_real (d ** f))
  => Ep d f = (E d (to_real f))%xr.
proof.
move=> rl_f smb_f; rewrite /Ep /= rl_f /= /psuminf smb_f /=; congr.
by apply: eq_sum => x /=; rewrite to_real_mdfun /= RField.mulrC.
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_dlet (d : 'a distr) (F : 'a -> 'b distr) f : 
  Ep (dlet d F) f = Ep d (fun x => Ep (F x) f).
proof.
pose D := dlet d F; case: (is_real (D ** f)); last first.
- move=> @{1}/Ep /= ^ + -> /= - /is_realPn [y] /=.
  case/md_eqinfP => [nz_Dy eqinf_fy].
  rewrite {1}/Ep /=; pose g x := mu1 d x ** Ep (F x) f.
  suff -> // : !is_real g; apply/is_realPn.
  case/supp_dlet: nz_Dy => x [x_d y_Fx]; exists x.
  apply/md_eqinfP; rewrite -/(_ \in _)%Distr x_d /=.
  rewrite /Ep /=; suff -> // : !is_real (F x ** f).
  by apply/is_realPn; exists y => /=; apply/md_eqinfP.
move=> isrl; have is_real_Fx_f: forall x, x \in d => is_real (F x ** f).
- move=> x x_d y /=; move/(_ y): isrl; case/md_realP; last first.
  - by move=> real_fy; apply/md_realP; right.
  rewrite ler_eqVlt ltrNge ge0_mu /= /D dlet1E sump_eq0P /=.
  - by move=> x'; apply: mulr_ge0.
  - by apply: summable_mu1_wght.
  by move/(_ x); rewrite RField.mulf_eq0 -supportPn x_d /= => ->.
pose fa (x : 'a) := mu1 d x.
pose fb (y : 'b) := to_real f y.
pose G x y := mu1 (F x) y.
have eqf: to_real (D ** f) = (fun y => sum (fun x => fa x * G x y) * fb y).
- by apply/fun_ext=> y; rewrite to_real_mdfun /= dlet1E.
have smb_Fx_f:
  (forall x, fa x <> 0%r => summable (fun y => G x y * fb y))
  => forall x, x \in d => summable (to_real (F x ** f)).
- move=> subsmb x x_d; have ->: to_real (F x ** f) = (fun y => G x y * fb y).
  - by apply/fun_ext=> y; rewrite to_real_mdfun /=.
  by apply/subsmb/gtr_eqF/x_d.
have eqE1:
  (forall x, fa x <> 0%r => summable (fun y => G x y * fb y))
  => forall x, x \in d => to_real (Ep (F x) f) = E (F x) (to_real f).
- move=> subsmb x x_d; rewrite EP_E /=.
  - by apply/is_real_Fx_f.
  - by apply/smb_Fx_f.
  - by rewrite to_pos_pos // &(exp_ge0) => y _; apply: to_realP.
case: (summable (to_real (D ** f))); last first.
- move=> smbN; rewrite {1}/Ep /= isrl /= /psuminf smbN /=.
  rewrite {1}/Ep /=; case _: (Lift.is_real _) => //=.
  move=> is_real_d_E_Fx_f @/psuminf. 
  case _: (summable _) => //=; apply/negP=> smb2N.
  apply: smbN; rewrite eqf; have := summable_swapR fa fb G _ _ _ _ _ => //.
  - by move=> y; apply/to_realP.
  - apply: eq_summable (smb2N) => /= x; rewrite to_real_mdfun /=.
    rewrite -/(fa x); case: (fa x = 0%r) => [-> //|nz_fa].
    congr => @/Ep /=; rewrite is_real_Fx_f /=; first by apply/supportP.
    rewrite /psuminf to_real_mdfun; case _: (summable _) => /=.
    - move=> _; rewrite to_pos_pos //= ge0_sum => y /=.
      by apply/mulr_ge0/to_realP/ge0_mu1.
    - by move/sum_Nsbl.
  - move=> x nz_fax; apply: contraLR is_real_d_E_Fx_f.
    move=> smb3N; apply/is_realPn => /=; exists x.
    apply/md_eqinfP; split; first by apply/supportP.
    rewrite /Ep /=; case: (Lift.is_real _) => //=.
    by rewrite /psuminf to_real_mdfun /= smb3N.
move=> ^smb0; rewrite eqf => smb.
have subsmb: forall y, fb y <> 0%r => summable (fun x => fa x * G x y).
- move=> y _; apply: summable_mu1_wght => x /=; split.
  - by apply: ge0_mu1.
  - by move=> _; apply: le1_mu1.
have [smb2 subsmb2] := summable_swap _ _ _ _ _ _ smb subsmb.
- by move=> x; apply: ge0_mu1.
- by move=> y; apply: to_realP.
- by move=> x y; apply ge0_mu1.
have {eqE1}eqE1 := eqE1 subsmb2.
have {smb_Fx_f}smb_Fx_f := smb_Fx_f subsmb2.
rewrite EP_E // /D; rewrite exp_dlet.
- by apply: eq_summable smb0 => x /=; rewrite RField.mulrC to_real_mdfun.
have is_real_d_E_Fx_f : is_real (d ** (fun x => Ep (F x) f)).
- move=> x /=; apply/md_realP; rewrite ler_eqVlt ltrNge ge0_mu1 /=.
  case: (x \in d) => [x_d | /supportPn -> //]; right.
  by rewrite /Ep /= is_real_Fx_f //= /psuminf smb_Fx_f.
apply: (eq_trans _ (E d (fun x => to_real (Ep (F x) f)))%xr).
- by do 2! congr; apply: eq_exp => x x_d /=; rewrite eqE1.
rewrite EP_E //=.
suff ->: to_real (fun x => mu1 d x ** Ep (F x) f) =
  (fun x => fa x * sum (fun y => G x y * fb y)) by apply/smb2.
apply/fun_ext => x /=; rewrite to_real_mdfun /=.
case: (x \in d); last by move/supportPn => @/fa ->.
move=> x_d; congr => //; rewrite eqE1 // /E.
by apply: eq_sum => /= y; rewrite RField.mulrC.
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_dmap (d:'a distr) (F: 'a -> 'b) (f: 'b -> xreal) : 
  Ep (dmap d F) f = Ep d (fun x => f (F x)).
proof. rewrite /dmap Ep_dlet; apply eq_Ep => x _ /=; apply Ep_dunit. qed.

(* -------------------------------------------------------------------- *)
lemma Ep_duniform ['a] (s : 'a list) (f : 'a -> xreal) :
  Ep (duniform s) f =
    of_reald (1%r / (size ((undup s)))%r) ** big predT f (undup s).
proof.
  rewrite (Ep_fin (undup s)) 1:undup_uniq.
  + move=> x hx; rewrite mem_undup -supp_duniform; smt(ge0_mu).
  rewrite mulr_sumr; apply eq_big_seq => /= x; rewrite mem_undup => hx.
  by rewrite duniform1E hx.
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_bool_gen (d : bool distr) (f : bool -> xreal) :
  Ep d f = mu1 d false ** f false + mu1 d true ** f true.
proof.
have -> := Ep_fin [false; true] d f //; 1: by move => [] //.
rewrite /big.
by have -> : map (d ** f) (filter predT [false; true]) =
  [(d ** f) false; (d ** f) true].
qed.

lemma Ep_dbool (f : bool -> xreal) :
  Ep {0,1} f = of_reald 0.5 ** f true + of_reald 0.5 ** f false.
proof.
  rewrite (Ep_fin [true; false]) 1://; 1: smt(supp_dbool).
  by rewrite big_consT big_seq1 /= !dbool1E.
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_dinterval (f : int -> xreal) i j:
  Ep [i..j] f = 
    (if i <= j then 1%r / (j - i + 1)%r else 0%r) ** 
       big predT f (range i (j + 1)).
proof.
  rewrite (Ep_fin (range i (j + 1))) 1:range_uniq. 
  + by move=> x; have := supp_dinter i j x; rewrite mem_range; smt (ge0_mu).
  rewrite mulr_sumr; apply eq_big_seq => x /mem_range hx /=.
  rewrite dinter1E /#.   
qed.

lemma Ep_dinterval_le (f : int -> xreal) (i j : int) :
  i <= j => 
  Ep [i..j] f = (1%r / (j - i + 1)%r) ** big predT f (range i (j + 1)).
proof. by move=> h; rewrite Ep_dinterval h. qed.

(* -------------------------------------------------------------------- *)
op (`|`) (b:bool) (x : xreal) = 
   if b then x else oo.

lemma cxr_true (x:xreal) : true `|` x = x
by [].
hint simplify cxr_true.

lemma cxrA (b1 b2 : bool) (f : xreal) : b1 `|` (b2 `|` f) = (b1 /\ b2) `|` f.
proof. rewrite /(`|`) /#. qed.
hint simplify cxrA.

lemma xle_cxr_r b (f1 f2 : xreal) : (b => f1 <= f2) => f1 <= (b `|` f2).
proof. by rewrite /(`|`); case:b. qed.

lemma xle_cxr_l b (f1 f2 : xreal) : b => f1 <= f2 => (b `|` f1) <= f2.
proof. move=> />. qed.

lemma xle_cxr b1 b2 (f1 f2 : xreal): 
  (b2 => (b1 /\ f1 <= f2)) => 
  (b1 `|` f1) <= (b2 `|` f2).
proof. move=> h; apply xle_cxr_r => /h />. qed.

lemma xle_cxr_b b1 b2 f : 
   (b1 => b2) =>
   b2 `|` f <= b1 `|` f.
proof. move=> h; apply xle_cxr_r => /h />. qed.

lemma xle_cxr_f b (f1 f2 : xreal) : 
   (b => f1 <= f2) =>
   b `|` f1 <= b `|` f2.
proof. by move=> h;apply xle_cxr => />. qed.

(* TODO: move this *)
lemma Rp_to_real_eq (x y : realp) : (x = y) <=> (to_real x = to_real y).
proof. by split=> [/>|/to_real_inj]. qed.

(* -------------------------------------------------------------------- *)
lemma Ep_cxr (d:'a distr) (b:'a -> bool) (f:'a -> xreal) : 
  Ep d (fun x => b x `|` f x) = 
  (forall x, x \in d => b x) `|` Ep d f. 
proof.
  rewrite /Ep /(`|`) /=. 
  case: (forall (x : 'a), x \in d => b x) => hb; last first. 
  + have /> x xin xb: exists x, x \in d /\ !b x by smt().
    have -> // : !is_real (fun (x0 : 'a) => mu1 d x0 ** if b x0 then f x0 else oo). 
    rewrite /is_real; apply /negP => h.
    by have := h x; rewrite xb /= /( ** ) /= Rp_to_real_eq /= /#.
  rewrite (eq_is_real_md _ _ f).
  + by move=> x /hb /= ->.
  case: (is_real (d ** f)) => // _; congr; apply fun_ext => x.
  rewrite /( **) Rp_to_real_eq /=; smt(ge0_mu1).
qed.

lemma if_cxr (b b1 b2:bool) (f1 f2: xreal) : 
  (if b then (b1 `|` f1) else (b2 `|` f2)) = 
  (if b then b1 else b2) `|` if b then f1 else f2.
proof. smt(). qed.

lemma if_cxr_l (b b1:bool) (f1 f2: xreal) : 
  (if b then (b1 `|` f1) else f2) = 
  (b => b1) `|` if b then f1 else f2
by smt().

lemma if_cxr_r (b b2:bool) (f1 f2: xreal) : 
  (if b then f1 else (b2 `|` f2) ) = 
  (!b => b2) `|` if b then f1 else f2
by smt().

lemma cxrDl b (f1 f2:xreal) : b `|` f1 + f2 = b `|` (f1 + f2).
proof. by rewrite /(`|`); case: b. qed.

lemma cxrDr b (f1 f2:xreal) : f1 + (b `|` f2)  = b `|` (f1 + f2).
proof. by rewrite /(`|`); case: b. qed.
hint simplify cxrDl, cxrDr.
(* FIXME: be able to add this 
 if_cxr, if_cxr_l, if_cxr_r.
*)

(* -------------------------------------------------------------------- *)
(* Concavity                                                            *)

op concave (f:xreal -> xreal) = 
  forall t, 0%r <= t <= 1%r =>
  forall x y, 
    t%xr * f x + (1.0 - t)%xr * f y <= f (t%xr * x + (1.0 - t)%xr * y).
   
lemma concave_cst (c:xreal) : concave (fun x => c).
proof. rewrite /concave /=; case: c => //= /#. qed.

lemma concave_id : concave (fun x => x).
proof. by rewrite /concave. qed.

lemma concaveD f1 f2 : 
  concave f1 => concave f2 => concave (fun x => f1 x + f2 x).
proof.
  rewrite /concave => h1 h2 t ht x y.
  apply: (Rpbar.xle_trans ((t%xr * f1 x + (1%r - t)%xr * f1 y)
                         + (t%xr * f2 x + (1%r - t)%xr * f2 y))).
  + rewrite !mulmDr -!addmA xler_addl (addmC (_ * f1 y) (Rpbar.(+) _ _)).
    by rewrite -!addmA xler_addl addmC.
  by apply xler_add;[ apply h1 | apply h2].
qed.

lemma concaveMr f c : 
  concave f => concave (fun x => f x * c).
proof.
  rewrite /concave => h t ht x y.
  rewrite !mulmA -mulmDl; apply/xler_mulr/h/ht.
qed.

lemma concaveMl f c : 
  concave f => concave (fun x => c * f x).
proof.
  rewrite /concave => h t ht x y.
  by rewrite !(mulmC c); apply (concaveMr f c h).
qed.

hint solve 0 concave : concave_cst concave_id concaveD concaveMr concaveMl.

(* TODO: add Jenshen inequality lemma *)

(* -------------------------------------------------------------------- *)
(* Increasing                                                           *)

op increasing (f:xreal -> xreal) = 
  forall (x y: xreal), x <= y => f x <= f y.

lemma increasing_cst (c:xreal) : increasing (fun x => c).
proof. rewrite /increasing /=; case: c => //= /#. qed.

lemma increasing_id : increasing (fun x => x).
proof. by rewrite /increasing. qed.

lemma increasingD f1 f2 : 
  increasing f1 => increasing f2 => increasing (fun x => f1 x + f2 x).
proof.
  rewrite /increasing => h1 h2; smt(xle_trans xler_add).
qed.

lemma increasingM f1 f2 : 
  increasing f1 => increasing f2 => increasing (fun x => f1 x * f2 x).
proof.
  rewrite /increasing => h1 h2; smt(xle_trans xler_mul).
qed.

hint solve 0 increasing : increasing_cst increasing_id increasingD increasingM.

(* -------------------------------------------------------------------- *)
(* Concave + Increasing                                                 *)

op concave_incr (f:xreal -> xreal) = 
  concave f /\ increasing f.

lemma concave_incr_cst (c:xreal) : concave_incr (fun x => c).
proof. split; [apply concave_cst | apply increasing_cst]. qed.

lemma concave_incr_id : concave_incr (fun x => x).
proof. split; [apply concave_id | apply increasing_id]. qed.

lemma concave_incrD f1 f2 : 
  concave_incr f1 => concave_incr f2 => concave_incr (fun x => f1 x + f2 x).
proof.
  by move=> [h1c h1i] [h2c h2i]; split; [apply concaveD | apply increasingD].
qed.

lemma concave_incrMr f c : 
  concave_incr f => concave_incr (fun x => f x * c).
proof.
  move=> [hc hi]; split; [apply concaveMr | apply increasingM] => //.
  apply increasing_cst.
qed.

lemma concave_incrMl f c : 
  concave_incr f => concave_incr (fun x => c * f x).
proof.
  move=> [hc hi]; split; [apply concaveMl | apply increasingM] => //.
  apply increasing_cst.
qed.

hint solve 0 concave_incr : 
  concave_incr_cst concave_incr_id.

hint solve 1 concave_incr :
  concave_incrD concave_incrMr concave_incrMl.

lemma concave_incr_cxr (b:bool) (f : xreal -> xreal) : 
  concave_incr f => concave_incr (fun x => b `|` f x).
proof. by case b. qed.

lemma concave_incr_if (b:bool) (f1 f2: xreal -> xreal) : 
  concave_incr f1 => concave_incr f2 => concave_incr (fun x => if b then f1 x else f2 x).
proof. by case b. qed.

hint solve 2 concave_incr : concave_incr_cxr concave_incr_if.

(* -------------------------------------------------------------------- *)
lemma trans_help P Q f : (P => Q) => (P `|` f) = oo \/ Q.
proof. case P => />. qed.
