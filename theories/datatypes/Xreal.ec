require import AllCore RealSeries List Distr StdBigop DBool DInterval Set List.  
require import StdOrder.
require Subtype Bigop.
import Bigreal Bigint RealOrder Biased.

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


lemma zK : 0%rp%r = 0%r.
proof. rewrite !of_realKd_ge0 ?addr_ge0 //.
qed.

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
proof.
  move => x; apply/to_real_inj; rewrite /(+) zK //=.
qed.  

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
proof.
move => x. apply/to_real_inj; rewrite /( *) (of_realKd_ge0 1%r) //.
qed.

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

hint simplify to_realD, to_realM , to_realI.

lemma of_realD x y : 0.0 <= x => 0.0 <= y => 
   (x + y)%rp = x%rp + y%rp.
proof. smt (of_realdK to_realP). qed.

lemma of_realM x y : 0.0 <= x => 0.0 <= y => 
   (x * y)%rp = x%rp * y%rp.
proof. smt (of_realdK to_realP). qed.

lemma of_realI (x:real) : (inv x)%rp = inv x%rp.
proof. smt (of_realdK to_realP  of_real_neg divr0). qed.
(* hint simplify of_realI. *) (* TODO !! loop with to_realI *)

op (%pos) (x:real) = if 0.0 <= x then x else 0.0.

lemma to_pos_pos (x:real) : 0.0 <= x => x%pos = x.
proof. by rewrite /(%pos) => ->. qed.
hint simplify to_pos_pos @10.

lemma le_pos (x y : real) : x <= y => x%pos <= y%pos
by smt().

lemma inv_pos x : inv x%pos = (inv x)%pos
by smt(divr0).

lemma to_real_of_real (x:real) : x%rp%r = x%pos.
proof. by rewrite to_real_of_reald witness_0 zK. qed.
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

lemma msmulmAC (x y :realp) (z : xreal) : x * y ** z = x ** (y ** z).
    proof.
  case (x = 0%rp) => [-> | hx ] //=.
  case (y = 0%rp) => [-> | hy ] //=.
  case z => [ r | ] //=; first by rewrite mulmA.
  rewrite /( **) hx hy //=. print of_reald_pinj.
  have -> : (x * y <> 0%rp). rewrite /( *). by smt(@Rp). (* ??? *)
  done.  
qed.  

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

hint simplify xle0x, xlexx_simpl, xlexoo_simpl.

lemma xltxx x : !x < x.
proof. by case: x. qed.

lemma xltxx_simpl x y : x = y => x < y = false.
proof. by move=> ->; rewrite xltxx. qed.

hint simplify xltxx_simpl.


lemma xle_trans (y x z : xreal) : x <= y => y <= z => x <= z.
proof. case: z => // z; case: y => // y; case: x => //=; smt(@Rp). qed.

lemma xlt_le_trans (y x z : xreal) : x < y => y <= z => x < z.
proof. case: z => //; case: y => //; case: x => //=; smt(@Rp). qed.

lemma xle_lt_trans (y x z : xreal) : x <= y => y < z => x < z.
proof. case: z => //; case: y => //; case: x => //=; smt(@Rp). qed.

lemma xle_tot (x y : xreal) : x <= y \/ y <= x.
proof. case: x => // x; case: y => // y; smt(@Rp). qed.

lemma xle_antisym (x y : xreal) : x <= y => y <= x <=> x = y.
proof. case: x => //; case: y => //; smt(@Rp). qed.

lemma xle_le  (a b : realp) : a%xr <= b%xr <=> to_real a <= to_real b.
proof. by []. qed.    

lemma nxlt_xle (x y : xreal) : !(y < x) <=> x <= y.
proof. by move=> *; case: (xle_tot x y) => //; smt(@Rp). qed.

lemma xle_nxlt (x y : xreal) : x <= y => !(y < x).
proof. by move=> *; case: (xle_tot x y) => //; smt(@Rp). qed.

lemma xle_eps (x y : xreal) :
  (forall eps, 0%r < eps => x <= y + eps%xr) => x <= y.
proof.
  move=> h.
  case: x h => [rx | ] h.
  - case: y h => [ry | ] h.
    + rewrite -nxlt_xle //=; apply contraT => *.
      have := h ((to_real rx - to_real ry) / 2%r) _; by smt().
    + by [].
  - case: y h => [ry | ] h => //.
    by have := h 1%r _ => //.
qed.

lemma xle_add_r x y : x <= x + y.
proof. case: x y => [x|] [y|] //=; smt(@Rp). qed.

lemma xle_add_l x y : x <= y + x.
proof. rewrite addmC xle_add_r. qed.

lemma xle_rle (x y : real) : 0%r <= x <= y => x%xr <= y%xr.
proof. by move => [??] /=; rewrite !to_pos_pos // &(ler_trans x). qed.

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
qed
.
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


lemma big_sub_le (f : 'a -> xreal) (I U : 'a list) :
  uniq I => (forall i, mem I i => mem U i) => 
  big predT f I <= big predT f U.
proof.
elim: I U => [| i I' IH] U.
- by move=> _ _ /=; rewrite big_nil.
- move=> /= [hniI' huniqI'] hsub.
  have hiU : mem U i by apply hsub; left.
  have hp : perm_eq U (i :: rem i U) by apply perm_to_rem.
  rewrite (eq_big_perm _ _ _ _ hp) !big_cons /predT //=.
  apply xler_addl; apply IH => //=.
  + move=> j hjI'. have := hsub j _. right. done.
    by smt( perm_eq_mem).
qed.

lemma big_le (f,g : 'a -> xreal) (P : 'a -> bool) (I : 'a list) :
    (forall a, P a => f a <= g a) => big P f I <= big P g I.
proof.
  move => h.    
  elim I.
  - by rewrite !big_nil.
  - move => a I IH.
  rewrite !big_cons; case (P a) => *; [apply xler_add; [exact (h a) | exact IH] | exact IH].
qed.
(* -------------------------------------------------------------------- *)

op xlub (P : xreal -> bool) : xreal.

axiom xlub_ub (P : xreal -> bool) (x : xreal) :
  P x => x <= xlub P.

axiom xlub_le (P : xreal -> bool) (b : xreal) :
    (forall x, P x => x <= b) => xlub P <= b.

lemma xlub_adherent (P : xreal -> bool) (c : xreal) :
  c < xlub P => (exists b, P b /\ c < b).
proof.
  move=> hzlt.
  apply/contraT => *.
  have hub : forall x, P x => x <= c by smt().
  have := xlub_le P c hub.
  smt().
qed.

lemma xle_xlub (P : xreal -> bool) (w x : xreal) :
  P w => x <= w => x <= xlub P.
proof. by move=> *; apply (xle_trans w); [ done | exact xlub_ub]. qed.


lemma xlt_xlub  (P : xreal -> bool)  (w x : xreal) :
  P w => x < w => x < xlub P.
proof. by move=> *; apply (xlt_le_trans w); [ done | exact xlub_ub]. qed.

lemma xlub_eq (B A : xreal -> bool) :
  (forall r, A r = B r) => xlub A = xlub B.
proof. move => *. congr; apply fun_ext. done. qed.

lemma xlub_mono (P Q : xreal -> bool) :
  (forall x, P x => Q x) => xlub P <= xlub Q.
  proof. by move=> h; apply xlub_le => x /h hQx; apply xlub_ub. qed.

lemma xlub_mono_dom (A B : xreal -> bool) :
  (forall a, A a => exists b, B b /\ a <= b) => xlub A <= xlub B.
proof.
  move=> hdom; apply xlub_le => a hAa.
  have [b [hBb hab]] := hdom a hAa.
  apply (xle_trans b); [exact hab | by apply xlub_ub].
qed.


lemma xlub_set0 : xlub set0 = 0%xr.
proof. apply xle_antisym. apply xlub_le => //=. done. qed.

lemma xlub_set1 x : xlub (set1 x) = x.
proof. apply xle_antisym; [by apply xlub_le | by apply xlub_ub]. qed.


lemma xlub_top (P : xreal -> bool) : P oo => xlub P = oo.
proof. move=> hPoo; apply xle_antisym; [done | exact xlub_ub]. qed.
  

lemma xlub_xlub (A : 'a -> bool) (S : 'a -> xreal -> bool) :
  xlub ((fun a => xlub (S a)) `$` A) = xlub (bigcup A S).
proof.
  apply xle_antisym.
  - apply xlub_le => z [a [hAa ->]].
    by apply xlub_le => w hSaw; apply xlub_ub; exists a.
  - apply xlub_le => z [a [hAa hSaz]].
    apply (xle_trans (xlub (S a))); first by apply xlub_ub.
    by apply xlub_ub; exists a.
qed.

lemma xlub_prod (A: 'a -> bool) (B : 'b -> bool) (f : 'a -> 'b -> xreal):
  xlub ((fun a => xlub ((fun b => f a b) `$` B)) `$` A)  = xlub ((fun (p : 'a * 'b) => f p.`1 p.`2) `$` (Set.(`*`) A B)).
proof.
  rewrite xlub_xlub prod_eq_bigcup bigcup_image //=.
  congr; rewrite /bigcup fun_ext => r.
  apply eq_iff; split.
  - move => [a [Aa //= /imageP [b [Bx -> ]]]].
    by exists b; rewrite /(`$`) Bx //=; exists (a,b); smt().
  - move => [b [bB /imageP [p [/imageP [a [Aa //= *]] *]]]]. 
    by exists a; rewrite /(`$`) Aa //=; exists p.`2; smt().
qed.


lemma xlub_addl (a : xreal) (P : xreal -> bool) :
  (exists p, P p) =>
  a + xlub P = xlub ((fun p => a + p) `$` P). 
proof.
move=> [p0 hp0].
  apply xle_antisym.
  - case: a => /=.
    + move=> ra.
      have Ecases : xlub P = oo \/ exists (rp : realp), xlub P = rp%xr by smt(). 
      case: Ecases => [Eoo | [lubP Efin]].
      * apply (xle_trans (xlub P)); first by rewrite Eoo; auto.
        apply xlub_mono_dom => x Px. exists (ra%xr + x) => //=.
        split; [ by exists x |  apply xle_add_l]. 
      * pose L := xlub ((+) ra%xr `$` P).
        apply nxlt_xle; apply negP => hlt.
        have [x Ex] : exists (x : realp), L = x%xr.
        by case: L hlt => [x | ] *; [exists x | smt()].
        move: hlt; rewrite Ex Efin => hlt.
        have *: ra%xr <= x%xr by rewrite -Ex; apply (xle_trans (ra%xr + p0)); [apply xle_add_r | apply xlub_ub; exists p0; auto ].
        have below : (x%r - ra%r)%xr < xlub P. smt(@Rp).
        have [p [hPp hpz]] := (xlub_adherent _ _ below).
        have * : ra%xr + p <= x%xr by rewrite -Ex; apply xlub_ub; exists p.
        smt(@Rp).
    + by apply xlub_ub; exists p0.
  - by apply xlub_le => z [p [hPp ->]] //=; apply xler_addl; apply xlub_ub.
qed.

lemma xlub_addr (a : xreal) (P : xreal -> bool) :
   (exists p, P p) =>
   xlub P + a = xlub ((fun p => p + a) `$` P).
proof.
  move=> hex.
  rewrite addmC (xlub_addl a P hex).
  by congr; smt(addmC).
qed.

lemma xlub_add (A B : xreal -> bool) :
  (exists a, A a) => (exists b, B b) =>
    xlub A + xlub B = xlub ((fun (p : xreal * xreal) => p.`1 + p.`2) `$` (A `*` B)).
proof.
  move=> [a aA] [b bB].
  rewrite xlub_addl; first by exists b.
  have ->: xlub ((fun (p : xreal) => xlub A + p) `$` B)
               = xlub ((fun p => xlub ((fun q => q + p) `$` A)) `$` B).
                + congr; apply fun_ext => q; apply eq_iff; apply exists_eq => x //=.
                 by rewrite -xlub_addr; first by exists a.
  rewrite xlub_xlub prod_eq_bigcup bigcup_image.
  by congr; apply bigcup_eq => r //= Br; apply fun_ext => s; rewrite !imageP; smt().
qed.

lemma xlub_bigsum (f : 'a -> xreal set) (J : 'a list) :
  uniq J => (forall a, mem J a => nonempty (f a)) =>
  big predT (fun a => xlub (f a)) J =
    xlub ((fun g => big predT g J) `$` (mem J `->` f)).
elim: J => [| a J' IH].
- move=> _ _ /=.
  rewrite big_nil.
  have -> : (mem [] `->` f) = setT by rewrite /(`->`).
  have -> : (fun (g : 'a -> xreal) => big predT g []) = (fun g => 0%xr).
  - by rewrite fun_ext => g /=; rewrite big_nil.
  by rewrite image_const //= xlub_set1.  
- move=> [aU J'u] hnE.
  rewrite big_cons /predT //=.
  have * : forall (a0 : 'a), a0 \in J' => exists (a1 : xreal), f a0 a1 by smt(). 
  have * : nonempty (f a) by smt().
  rewrite IH //=.
  have * :  nonempty ((fun (g : 'a -> xreal) => big predT<:'a> g J') `$` (mem J' `->` f)).
    + exists (big predT (fun a' => choiceb (f a') witness) J').
      apply/imageP; exists (fun a' => choiceb (f a') witness); split; [| done].
      by rewrite /(`->`) => a' ha'; apply (choicebP (f a') witness); smt().
  rewrite xlub_add //=.
  congr; rewrite fun_ext => z /=; rewrite /(`$`) eq_iff //= .  
  split.
  - move=> [p]; rewrite /(`*`); move => [[fap1 [g [gg ->]]]] ->.
    exists (fun a' => if a' = a then p.`1 else g a'); rewrite /(`->`).
    split. 
    + move=> a' ha'. case: (a' = a) => [-> //= |]; by smt().
    + rewrite big_cons /=.
      congr; apply eq_big_seq => a' ha' /=. by smt().
  - move=> [g [hg ->]].
    exists (g a, big predT g J'); rewrite /(`*`) //=.
    split; [split; [smt() | exists g => //=; smt()] | by rewrite big_cons].
qed.    

lemma xlub_mull (c : realp) (P : xreal -> bool) :
  0%rp < c =>
  c%xr * xlub P = xlub ((fun x => c%xr * x) `$` P) .
proof.
  move=> c_nneg.
  have hmul1 : (inv c)%xr * c%xr = 1%xr by smt(of_realdK to_realP).
  have invc_nneg: 0%rp < inv c. smt(@Rp).
  apply xle_antisym.
  - apply (xler_pmul2l _ invc_nneg); rewrite mulmA hmul1 //=.
    apply xlub_le => x hPx.
    apply (xle_trans ((inv c)%xr * (c%xr * x))).
    * by rewrite mulmA hmul1. 
    apply xler_mull; apply xlub_ub.
    by apply imageP; exists x.
  - apply xlub_le => z /imageP [x [hPx ->]] //=.
    apply (xler_pmul2l _ c_nneg). exact xlub_ub.
qed.

lemma xlub_mulr (c : realp) (P : xreal -> bool) :
  0%rp < c =>
  xlub P * c%xr = xlub ((fun x => x * c%xr) `$` P) .
proof.
  move=> c_nneg.
  rewrite mulmC xlub_mull //.
  by congr; smt(mulmC).
qed.    

lemma xlub_scale_mdl (c :realp) (P : xreal -> bool) :
  c ** xlub P = xlub (( ** ) c `$` P). 
proof.
  case ( (c = 0%rp) ) => [-> //= | hc].
  * case (empty P) => [ /empty_set0 -> | /negb_forall //= [x px]]; first by rewrite image_set0 xlub_set0.
    rewrite /(`$`) //= (xlub_eq (set1 0%xr)).
    + by move => r //=; apply eq_iff; split; [  | move => <-; exists x]. 
    by rewrite xlub_set1.
  + have : (0%rp < c) by smt(@Rp).
    by rewrite /( ** ) hc //=; exact xlub_mull.
qed.  

(* xsum *)


op xsum  (s : 'a -> xreal) : xreal = xlub (big predT s `$` uniq).



lemma xsum_eq (g f : 'a -> xreal) :
  (forall a, f a = g a) => xsum f = xsum g.
proof.
  move=> hfg; apply xlub_eq => r /=.
  by apply/eq_iff; split=> [/imageP [J [huJ ->]] | /imageP [J [huJ ->]]] //=;
     apply/imageP; exists J; split=> //; apply eq_big_seq => a _ /=; rewrite hfg.
qed.

lemma xsum_le (f g : 'a -> xreal) :
  (forall a, f a <= g a) => xsum f <= xsum g.
proof.
  move=> hfg; apply xlub_mono_dom => r /imageP [J [huJ ->]].
  exists (big predT g J); split.
  - apply/imageP; exists J; split=> //.
  - by apply big_le.
qed.

lemma xsum_inj_le (s : 'a -> xreal) (h : 'b -> 'a) :
  injective h => xsum (s \o h) <= xsum s.
proof.
  move=> hinj; apply xlub_le => z /imageP [Jb [huniqJb ->]].
  apply xlub_ub; apply/imageP; exists (map h Jb); rewrite big_map //=.
  rewrite map_inj_in_uniq //=.
  - move => x y hx hy; exact hinj. 
qed.

lemma xsum_reindex (s : 'a -> xreal) (h : 'b -> 'a) (h' : 'a -> 'b) :
  injective h => cancel h' h => xsum s = xsum (s \o h).
proof.
  move=> hinj hK.
  apply xle_antisym.
  - have h'inj : injective h' by move=> x y heq; rewrite -(hK x) -(hK y) heq.
    have {1}<- : (s \o h) \o h' = s by rewrite fun_ext /(\o) => y //=; rewrite hK.
    apply (xsum_inj_le); exact h'inj.
  - exact (xsum_inj_le s h hinj).
qed.

lemma xsum_oo (f : 'a -> xreal) (a : 'a) : f a = oo => xsum f = oo.
proof.
  move => ha.
  apply xle_antisym => //=.
  apply xlub_ub; apply/imageP.
  by exists [a]; rewrite big_cons /predT big_nil  ha. 
qed.

lemma xsum_0 (f : 'a -> xreal) : (forall (a : 'a), f a = 0%xr) => (xsum f = 0%xr).
proof.
  + move => hf. apply xle_antisym.
    * by apply xlub_le => x /imageP [L [uL ->]]; rewrite big1 //.
    * by apply xlub_ub; exists [].
qed.

lemma xsum_0P (f : 'a -> xreal) : (xsum f = 0%xr) <=> (forall (a : 'a), f a = 0%xr).
  split.  
  + move => hf a; apply xle_antisym. 
    * by rewrite -hf; apply xlub_ub; exists [a]; rewrite big_cons big_nil /predT. 
    * done.
  exact xsum_0.
qed.

(*
lemma xsum_ne0 (f : 'a -> xreal) : (exists (a : 'a), f a <> 0%xr) => (xsum f <> 0%xr).
    smt(xsum_0P).
qed.

lemma xsum_ne0P (f : 'a -> xreal) : (xsum f <> 0%xr) <=> (exists (a : 'a), f a <> 0%xr).
proof. smt(xsum_0P). qed.
    *)

(* -------------------------------------------------------------------- *)
lemma xsum_fin J f : 
  uniq J => 
  (forall (a : 'a), f a <> 0%xr => a \in J) =>
  xsum f = big predT f J.
proof.
  move => uJ fJ.  
  apply xle_antisym.
  * apply xlub_le => x /imageP [L [uL ->]].
    rewrite (bigID _ _ (fun a => a \in J)).
    rewrite (big1_seq (fun (x0 : 'a) => ! (x0 \in J))) //=.
    + by move=>a; apply absurd; move => h; rewrite (fJ _ h).
    rewrite -big_filter.
    apply big_sub_le; first by exact: filter_uniq.
    by move => a /mem_filter.
  by apply xlub_ub; exists J.
qed.
  
    (* todo *)
lemma to_real_is_real (x : xreal) : is_real x => (to_real x)%xr = x.
proof. case x; smt(of_realdK to_realP). qed.
  

lemma to_real_is_realF (f : 'a -> xreal) (a : 'a) : is_real f => (to_real f a )%xr = f a.
proof. smt(to_real_is_real). qed.
(*end*)

lemma xsum_neq_oo (f : 'a -> xreal) :
    xsum f <> oo <=> (is_real f /\ summable (to_real f)).
proof.
  split.
  - move=> fin.
    have ir_f: is_real f by move: fin; apply contraR => [/is_realPn [a ha]]; exact (xsum_oo _ _ ha).
    rewrite ir_f //=.
    have [M [ubM M_ge0]] : exists (M : real), xsum f = M%xr /\ 0%r <= M. 
      case (xsum f) fin; [move => rp *; by exists (to_real rp) | done].
    exists M => J uJ.
    have //= : (BRA.big predT<:'a> (fun (i : 'a) => `|to_real f i|) J)%xr <= M%xr.
    + rewrite -ubM -bigXR; first by move => * /=; exact normr_ge0.
      apply (xle_xlub _ (BXA.big predT f J)).
      - apply/imageP; exists J => //.
        apply big_le => a _ //=; rewrite ger0_norm //=; first by exact to_realP.
        by rewrite to_real_is_realF //.
    by rewrite (to_pos_pos M) //; smt(). 
  - move => [irf [M hM]].
    have //= : xsum f <= M%xr.
    + apply xlub_le => x /imageP [J [uJ ->]].
      apply (xle_trans (BRA.big predT<:'a> (fun (i : 'a) => `|to_real f i|) J)%xr).
      + rewrite -bigXR; first by move => * /=; exact normr_ge0.
        by apply big_le => a _ //=; rewrite ger0_norm ?to_realP //= to_real_is_realF //.
      simplify; apply le_pos; exact (hM J uJ). 
    by case (xsum f).     
qed.

    
lemma xsum_fin_sum (f : 'a -> xreal) :
  is_real f => summable (to_real f) => xsum f = (sum (to_real f))%xr.
  move => ir sf; rewrite /sum sf //=.
  have ->: neg (to_real f) = fun _ => 0%r.
  have f_nneg: forall a, 0%r <= to_real f a by smt(to_realP).
    + apply fun_ext => a; by smt().
    have -> /=: psum (fun (_ :'a) => 0%r) = 0%r by apply psum_eq0P; [exact summable0 | done].
  case (xsum f = oo); first by smt(xsum_neq_oo).
  move => xsum_fin.  
  have [M [ubM M_ge0]] : exists (M : real), xsum f = M%xr /\ 0%r <= M by case (xsum f) xsum_fin; [move => rp *; by exists (to_real rp) | done].
  apply xle_antisym.
  - apply xlub_le => x /imageP [J [uJ ->]].
    have -> : pos (to_real f) = to_real f by apply fun_ext => a /=; smt(to_realP).
    have -> : big predT f J = big predT (fun a => (`|to_real f a|)%xr) J.
    by apply eq_big_seq => a _ //=; rewrite ger0_norm ?to_realP to_real_is_realF //.
    rewrite bigXR //=; first by move => * /=; exact normr_ge0.
    apply le_pos; exact (ler_big_psum (to_real f) J sf uJ). 
  - rewrite ubM //=; apply le_pos.
    apply ler_psum_lub => J uJ.
    rewrite (BRA.eq_big_seq _ (to_real f)); first by smt(ger0_norm to_realP).
    have : big predT (fun x => (to_real f x)%xr) J <= M%xr.
    + rewrite -ubM; apply xlub_ub.
      exists J; rewrite uJ //=.
      apply eq_big_seq => a _ //=;  exact to_real_is_realF. 
    rewrite bigXR //=; first by move => * //=; exact to_realP.
    by smt().
qed.

lemma xsumD (f g : 'a -> xreal) : xsum (f + g) = xsum f + xsum g.
proof.    
  rewrite xlub_add; [by exists 0%xr; exists [] | by exists 0%xr; exists [] | ].
  rewrite /xsum; apply xle_antisym.
  + apply xlub_mono_dom => x //=.
    move => [J [uJ xs]].
    exists x => //=; rewrite imageP.
    exists (big predT f J, big predT g J); rewrite prodP //= -big_split xs //=.
    by split; exists J => //=.
  + apply xlub_mono_dom => x //=.
    move=> /imageP [[a b] [/prodP [/imageP [I [uI ->]] /imageP [J [uJ ->]]] ->]].
    pose U := undup (I ++ J).
    exists (big predT (f + g) U).
    split.
    + exists U; split; [exact (undup_uniq _) | done].
    + apply (xle_trans (big predT f U + big predT g U)); last by rewrite big_split.
      apply xler_add; apply big_sub_le => //=; move => *; rewrite mem_undup mem_cat;
      [by left | by right].  
qed.

  

(* todo *)
lemma undup_nseq (n : int) (a : 'a) : undup (nseq n a) = if n <= 0 then [] else [a].
proof.
  move: n; apply natind => n nleq0 //=.
  - rewrite nseq0_le //= /#.
  - by move => IH; rewrite nseqS // //= IH mem_nseq; smt(). 
qed.

lemma undup_cat (s t : 'a list) :
  (forall x, x \in s => ! x \in t) =>
    undup (s ++ t) = undup s ++ undup t.
proof.
  elim s; first by auto.  
  move => x l IH h //=.
  case (x \in l) => hxl. rewrite mem_cat hxl //=.
  apply IH. by smt().
  rewrite mem_cat hxl.
  have hxt : ! (x \in t) by smt().
  rewrite hxt IH; first by smt() .
  by [].
qed.

op concatmap (f : 'a -> 'b list) (l : 'a list) : 'b list = flatten (map f l).

lemma concatmap_nil ['a, 'b] (f : 'a -> 'b list) : concatmap f [] = [].
proof. by rewrite /concatmap. qed.

lemma concatmap_cons ['a, 'b] (f : 'a -> 'b list) (x : 'a) (s : 'a list) :
  concatmap f (x :: s) = f x ++ concatmap f s.
proof. by rewrite /concatmap /= flatten_cons. qed.

lemma unzip1_cat (s t : ('a * 'b) list) :
  unzip1 (s ++ t) = unzip1 s ++ unzip1 t.
    proof. by elim s => //= x s ih. qed.

lemma inj_pswap : injective pswap<:'a, 'b>.
proof. by move => x y heq; rewrite -(pswapK x) -(pswapK y) heq. qed.



(* end todo*)

op grid (I : 'a -> 'b list) (J : 'a list) = concatmap (fun a => map (fun b => (a,b)) (I a)) J.

lemma grid_uniq (I : 'a -> 'b list) (J : 'a list) :
  uniq J => (forall a, mem J a => uniq (I a)) =>
  uniq (grid I J).
proof.
elim: J => [| a J' IH].
- by move=> _ _ /=. 
- move=> /= [aneJ uJ] uI.
  rewrite /grid /concatmap /= flatten_cons cat_uniq.
  split.
  + apply (map_inj_in_uniq (fun b => (a,b))).
    + move=> b1 b2 b1' b2' /=. done.
   by apply (uI a).
  split. 
  + rewrite hasPn => p.
    move=> /flatten_mapP [a' [ha' /mapP [b' [hb' hpeq]]]].
    apply/negP => /mapP [b [hb /=]].
    by smt().
  by rewrite IH; smt().
qed.

lemma grid_cons (a : 'a) (I : 'a -> 'b list) (J : 'a list):
  grid I (a :: J) = map (fun b => (a,b)) (I a) ++ grid I J.
proof. by rewrite /grid /concatmap_cons. qed.    

lemma grid_filter_nil (a : 'a) (I : 'a -> 'b list) (J : 'a list) : 
    ! mem J a => filter (fun (xy : 'a * 'b) => xy.`1 = a) (grid I J) = [].
proof.
  elim J; first by done.    
  move=> x J' IH /= /negb_or [anex aniJ'].
  rewrite grid_cons filter_cat filter_map /preim //=.
  have ->: (fun (_ : 'b) => x = a) = pred0 by smt().
  rewrite filter_pred0 //=. exact (IH aniJ').
qed.

lemma filter_grid (a : 'a) (I : 'a -> 'b list) (J : 'a list) :
  uniq J =>
  mem J a =>
  filter (fun xy : 'a * 'b => xy.`1 = a) (grid I J) = map (fun b => (a,b)) (I a). 
proof.
  elim J; first by done.    
  move => x J' IH /= [aneJ uJ'] aJ.
  rewrite grid_cons filter_cat filter_map /preim.
  move:  aJ aneJ IH. case (a = x) => [<- //= | //=].
  - by move => aneJ' _; rewrite grid_filter_nil // cats0 filter_predT.
  - move => anex ainJ' xneJ' IH.
    rewrite IH // //.
    have ->:  (fun (_ : 'b) => x = a) = pred0 by smt().
  by rewrite filter_pred0 //=.
qed.


lemma grid_filter_nonempty (I : 'a -> 'b list) (J : 'a list) :
  grid I J = grid I (filter (fun a => I a <> []) J).
proof.
  elim: J => [| a J' IH] //=.
  rewrite grid_cons IH; case: (I a = []) => hIa /=; [ by rewrite hIa | by rewrite grid_cons ]. 
qed.

lemma undup_unzip1_grid (I : 'a -> 'b list) (J : 'a list) :
  uniq J =>
  (forall a, mem J a => I a <> []) =>
  undup (unzip1 (grid I J)) = J.
proof.
  elim J; first by done.
  move => a J' IH /= [aneJ uJ'] aJ.
  rewrite grid_cons unzip1_cat.
  have ->: forall l, unzip1 (map (fun (b : 'b) => (a, b)) l) = nseq (size l) a.
  + move => l; elim l => //=; first by rewrite nseq0.
    move => l ->; rewrite -nseqS; first by exact size_ge0.
    congr; smt(). 
  rewrite undup_cat.
  + move => b.
    rewrite mem_nseq -mem_undup.
    move => [sz <-].
    have aJ': forall (a0 : 'a), a0 \in J' => I a0 <> [] by move => c; have :=aJ c; case (c=a) => //=.
    by rewrite (IH uJ' aJ').  
  rewrite undup_nseq IH //.
  + move => b. have:=aJ b; case (b = a) => //=.
  have -> //= : !(size (I a) <= 0) by have //= := aJ a; case (I a) => //=; smt(size_ge0).
qed.

lemma xsum_pair (s : 'a * 'b -> xreal): xsum s = xsum (fun a => xsum (fun b => s (a, b))).
proof.
  apply xle_antisym.
  - apply xlub_le => z /imageP [J [uJ ->]].
    pose Ja := undup (map fst J).
    pose Jb a := map snd (filter (fun (p : 'a * 'b) => p.`1 = a) J).
    have uJa : forall a, uniq (Jb a).
    - move => a; rewrite /Jb map_inj_in_uniq.
      + move=> p1 p2 hp1 hp2 //= heq.
        have hp1a : p1.`1 = a by move: hp1; rewrite mem_filter => -[]. 
        have hp2a : p2.`1 = a by move: hp2; rewrite mem_filter => -[].
        by rewrite (pairS p1) (pairS p2) hp1a hp2a heq.
      + by apply filter_uniq.
    have -> : big predT s J = big predT (fun a => big predT (fun b => s (a,b)) (Jb a)) Ja.
    * rewrite (partition_big fst predT predT s J Ja (undup_uniq _)).
      + move => p Jp _ => //=; split => //=; 
        by rewrite mem_undup; apply mem_map_fst; exists p.`2; smt().
      + apply eq_big_seq => a Jaa //=.
        rewrite -big_filter /Jb.
        have -> : (fun (y : 'a * 'b) => predT y /\ y.`1 = a) = (fun (y : 'a * 'b) => y.`1 = a) by smt().
        rewrite (eq_big_seq _ (fun (y : 'a * 'b) => s (a, y.`2))).
        by move => y hy; rewrite mem_filter in hy; smt().
        by rewrite big_map //=.
    apply (xle_trans (big predT (fun (a : 'a) => xsum (fun (b : 'b) => s (a, b))) Ja)).
    * apply big_le => a _ //=. apply xlub_ub; rewrite /(`$`). exists (Jb a) => //=; by apply uJa.
    * apply xlub_ub; rewrite /(`$`). by exists Ja; split; first by apply undup_uniq. 
  - apply xlub_le => zz /imageP [J [uJ ->]].
    rewrite xlub_bigsum // => //=.
    - by move => a Ja; exists (big predT (fun b => s(a,b)) []); rewrite /(`$`); exists [].  
    apply xlub_le => z /imageP [g [/funsetP gSpec ->]].
    pose I a := choiceb (fun l => uniq l /\ g a = big predT (fun b => s (a,b)) l) [].
    have ISpec : forall a, mem J a => uniq (I a) /\
                               g a = big predT<:'b> (fun (b : 'b) => s (a, b)) (I a).
    - move=> a haJa.
      apply (choicebP (fun l => uniq l /\ g a = big predT (fun b => s (a,b)) l)). 
      by rewrite /P; have:= gSpec a haJa; rewrite /(`$`) //=.
    have I_uniq: forall a, a \in J => uniq (I a) by smt().
    have I_ix_g: forall a, a \in J => g a = big predT<:'b> (fun (b : 'b) => s (a, b)) (I a). by smt().
    (* have gSpecrid_uniq : uniq (grid I J). apply (grid_uniq _ _ uJ). gsmt(). *)

     
    have //= ->: big predT g J = big (fun a => a \in J /\ I a <> []) g J.
    + rewrite big_seq (bigID (mem J) _ (fun a => I a <> []) _) /predI /predC.
      have //= -> : big (fun a => (a \in J) /\ ! (I a <> [])) g J = 0%xr.
      - apply big1 => a [haJ hIa].
        have hIa0 : I a = [] by smt().
       by have [_ ->] := ISpec a haJ; rewrite hIa0 big_nil.
    by smt().
    rewrite -big_filter.
    have -> : filter (fun a => (a \in J) /\ I a <> []) J = filter (fun a => I a <> []) J
    by apply eq_in_filter => a haJ /=; smt().
    have //= -> : big predT g (filter (fun (a : 'a) => I a <> []) J) = big predT s (grid I J).
    + rewrite (big_pair s) //=; first by rewrite grid_uniq // //.
      rewrite grid_filter_nonempty.
      rewrite undup_unzip1_grid; first by apply filter_uniq.    
      - by move => a /mem_filter //=.
      apply eq_big_seq => a haJa /=.
      rewrite filter_grid //; first by apply filter_uniq.
      rewrite big_map I_ix_g //.
      by move: haJa; rewrite mem_filter => -[_ ->].
    apply xlub_ub; apply/imageP.
    by exists (grid I J); rewrite grid_uniq.
qed.

lemma xsum_exchange (s : 'a -> 'b -> xreal) :
  xsum (fun a => xsum (fun b => s a b)) = xsum (fun b => xsum (fun a => s a b)).
proof.
  pose t (p : 'a * 'b) := s p.`1 p.`2.
  rewrite -(xsum_pair t).
  rewrite (xsum_reindex t pswap pswap) /t /(\o) /pswap //=; [exact inj_pswap | exact pswapK |  ].
  by rewrite xsum_pair.
qed.

lemma xsum_scale_mdl (c : realp) (f : 'a -> xreal):
   c ** xsum f = xsum (fun a => c ** f a) .
proof.     
  rewrite xlub_scale_mdl.
  rewrite /xsum image_comp.
  by congr; apply image_eq_in => L _ //=; exact mulr_sumr. 
qed.

lemma xsum_mull (c : realp) (f : 'a -> xreal):
   0%rp < c => c%xr * xsum f = xsum (fun a => c%xr * f a) .
proof.     
  move => hc. have md: forall a, c%xr * a = c ** a by smt().
  rewrite md (xsum_eq (fun a => c ** f a) (fun a => c%xr * f a)).
    by move => a //=; exact md.
  exact xsum_scale_mdl. 
qed.

lemma xsum_mulr (c : realp) (f : 'a -> xreal):
   0%rp < c => xsum f * c%xr = xsum (fun a => f a * c%xr) .
proof.
  move => hc.
  rewrite mulmC.
  have ->: (fun a => f a * c%xr) = (fun a => c%xr * f a)
    by apply fun_ext; move => a //=; exact mulmC.
  exact xsum_mull.
qed.




op Ep (d : 'a distr) (f : 'a -> xreal) : xreal =
  xsum (fun a => (mu1 d a) ** f a).

lemma eq_Ep ['a] (d : 'a distr) (f g : 'a -> xreal) :
  (forall (x : 'a), x \in d => f x = g x) => 
  Ep d f = Ep d g.
proof. by rewrite /Ep /= => /eq_md ->. qed.

lemma le_Ep ['a] (d: 'a distr) (f g : 'a -> xreal) : 
   (forall (x : 'a), x \in d => f x <= g x) => 
  Ep d f <= Ep d g.
proof.
  by rewrite /Ep /= => h; apply xsum_le => a //=; apply/xler_md/h.
qed.

lemma EpC ['a] (d : 'a distr) (c : xreal):
   Ep d (fun (_ : 'a) => c) = (weight d) ** c.
proof.
  have to_real_mdfun': forall (f : 'a -> xreal), to_real (d ** f) = fun (x : 'a) => to_real (f x) * mu1 d x. 
    by move => f; rewrite to_real_mdfun; apply fun_ext => a; apply RField.mulrC.    
  rewrite /Ep; case: c => [c | ].
  + rewrite xsum_fin_sum //.
    + rewrite to_real_mdfun' //=.
      exact (summableZ _ _ (summable_mu1 d)).
    rewrite to_real_mdfun' //=.
    by rewrite mulmC sumZ /= of_realM // 1: ge0_sum //= weightE; do 3! congr.
  case (exists a, 0%r < mu1 d a) => [[a ha] | /negb_exists //= ha].
  + rewrite (xsum_oo _ a); first by smt(@Rp).
    rewrite eq_sym; apply md_eqinfP => //=.
    by smt(weight_eq0 ge0_weight).
  have mu1_0: forall a, mu1 d a = 0%r by smt(ge0_mu1).
  have -> //= : weight d = 0%r. rewrite weightE; rewrite sump_eq0P // ?summable_mu1.
  apply xsum_0.
  by move => a //=; rewrite mu1_0.
qed.

lemma EpsZ ['a] (d: 'a distr) (c:realp) (f: 'a -> xreal) :
  Ep d (fun x => c ** f x) = c ** Ep d f.
proof.
  rewrite /Ep xsum_scale_mdl.
  by apply xsum_eq => a //=; rewrite /( ** ); smt(@Rp). 
qed.

lemma EpZ ['a] (d: 'a distr) (c:realp) (f: 'a -> xreal) :
  c <> of_reald 0.0 => 
  Ep d (fun x => rp c * f x) = rp c * Ep d f.
proof.
  move=> hc. rewrite /Ep xsum_mull; first by smt(@Rp).
  apply xsum_eq => a //=. rewrite /( ** ). smt(@Rp).
qed.


lemma EpD ['a] (d : 'a distr) (f1 f2 : 'a -> xreal) : 
  Ep d (f1 + f2) = Ep d f1 + Ep d f2.
proof.
  rewrite /Ep -xsumD.
  by apply xsum_eq => a //=; exact smulmDr. 
qed.


lemma summable_to_pos (f : 'a -> real) : summable f => summable (fun x => (f x)%pos).
proof.
 have -> : (fun x => (f x)%pos) = (fun x => pos f x).
 by apply fun_ext => a; smt().
  exact : summable_pos.
qed.

lemma Ep_mu (d:'a distr) (p:'a -> bool): 
  Ep d (fun a => (p a)%xr) = (mu d p)%xr.
proof.
  rewrite /Ep.
  rewrite (: (fun (x : 'a) => ((mu1 d x)%rp * (b2r (p x))%rp)%xr) = (d ** (fun x => (p x)%xr))) 1://.
  have ir : is_real (d ** fun (x : 'a) => (p x)%xr) by apply is_real_sM.
  rewrite xsum_fin_sum // /to_real //=.
  + apply summable_mu1_wght => a //=; smt().
  by congr; rewrite muE; apply eq_sum => x /=; case: (p x). 
qed.

(* -------------------------------------------------------------------- *)
lemma Ep_fin ['a] J (d : 'a distr) f : 
  uniq J => 
  (forall (x : 'a), mu1 d x <> 0%r => x \in J) =>
  Ep d f = big predT (d ** f) J.
proof.
  move=> uJ hJ; rewrite /Ep /=.
  apply (xsum_fin _ _ uJ). 
  by move=> a //=; case (mu1 d a = 0%r) => [-> | /hJ].
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
  move => rl_f smb_f. rewrite /Ep xsum_fin_sum // //=. congr.
  by apply: eq_sum => x /=; rewrite to_real_mdfun /= RField.mulrC.
qed.



op ( *** ) ( c x : xreal) : xreal =
  if c = 0%xr then 0%xr else x * c.


lemma xsum_scale_mdr (f : 'a -> realp) (c : xreal) :
    xsum (fun (x : 'a) => (f x)%xr) <> oo => xsum (fun (x : 'a) => f x ** c) = xsum (fun (x : 'a) => (f x)%xr) *** c.
proof.
  move => summ.    
  case: (xsum (fun (x : 'a) => (f x)%xr) = '0) => hf. 
  - rewrite hf.
    have hall0:= iffLR _ _ (xsum_0P _) hf.
    by rewrite xsum_0; first by move => a //=; smt().
  rewrite /( *** ) hf //=.
  case (c = 0%xr) => [-> | ].
  + rewrite xsum_0; first by move => a //=.
    smt(@Rp).
  case c => [cr //= hc| hc].
  + rewrite xsum_mull; first by smt(@Rp).
    by apply xsum_eq => a //=; smt(@Rp).
  have [a ha] : (exists a, (f a)%xr <> 0%xr). by move: hf; by smt(xsum_0P @Rp).
  apply xle_antisym => //=.
  apply xlub_ub; rewrite imageP. by exists [a]; rewrite big_cons big_nil //=; smt().
qed.  
  
(* -------------------------------------------------------------------- *)
lemma Ep_dlet (d : 'a distr) (F : 'a -> 'b distr) f : 
  Ep (dlet d F) f = Ep d (fun x => Ep (F x) f).
proof.
  rewrite /Ep /mlet //=.
  have mconv: forall (a :realp) (b : xreal), a ** b = a%xr *** b by rewrite /( **) /( ***) //=; smt().
  rewrite (xsum_eq (fun (y : 'b) => xsum (fun (x : 'a) => (mu1 d x * mu1 (F x) y) ** f y))).
  + move => b //=; rewrite dlet1E.
    rewrite mconv.
    pose w a := (mu1 d a * mu1 (F a) b)%xr.
    have ->: (fun (a : 'a) => mu1 d a * mu1 (F a) b) = to_real w.
      by rewrite /w /to_real; apply fun_ext => a //=; smt(ge0_mu1).
    have sum_mus : summable (to_real w).
      by rewrite /w /to_real //=; apply summable_to_pos; apply summable_mu1_wght; move => a //=.
    have ir_mus : is_real w.
      by rewrite /is_real => a //=.
    rewrite -xsum_fin_sum // //.
    by rewrite xsum_scale_mdr; first by smt(xsum_neq_oo).
  rewrite xsum_exchange //=.
  apply xsum_eq => a //=.
  rewrite xsum_scale_mdl.
  apply xsum_eq => b //=.
  rewrite -msmulmAC /xmul //= /( *) //=.
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
lemma Ep_dbool (f : bool -> xreal) :
  Ep {0,1} f = of_reald 0.5 ** f true + of_reald 0.5 ** f false.
proof.
  rewrite (Ep_fin [true; false]) 1://; 1: smt(supp_dbool).
  by rewrite big_consT big_seq1 /= !dbool1E.
qed.

lemma Ep_dbiased (p : real) (f : bool -> xreal) :
  0%r <= p <= 1%r => Ep (dbiased p) f = p ** f true + (1%r - p) ** f false.
proof.
  move=> ?; rewrite (Ep_fin [true; false]) //; 1: by case.
  by rewrite /BXA.big /predT /= !dbiased1E /= !clamp_id //.
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
  case: (forall (x : 'a), x \in d => b x) => [hall | /negb_forall [x //= /negb_imply [/supportP mux nbx]]].
  + apply xsum_eq. move => a //=.
    case (a \in d); first by move => ha; rewrite (hall _ ha) //=.
    move => /supportPn -> //=.
  apply (xsum_oo _ x) => //=.
  rewrite nbx /( **) //=.
  by smt(@Rp). 
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

