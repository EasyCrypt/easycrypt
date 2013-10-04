require import Prime_field.
require import Cyclic_group_prime.
require Int.
require import FSet.
require import Bool.
require import Real.

import Dgroup.
import Dgf_q.

(* axioms *)
axiom gen_exp_inj : forall(m n : gf_q), g ^ m = g ^ n => m = n.
axiom neg_distr : forall (x y : gf_q), -(x + y) = -x + -y.
axiom neg_zero : forall (x y : gf_q), gf_q0 = x - y => x = y.

(* lemmas of groups and prime field *)
lemma gen_def : forall X, exists m, X = g ^ m. 
proof.
 intros X; exists (log X).
 by rewrite group_log_pow.
save.

const I : group = g ^ gf_q0.

lemma exp_inj : forall X (m n : gf_q), X <> I => X ^ m = X ^ n => m = n.  
proof.
 intros => X m n.
 cut [r ->] := gen_def X.
 case (r = gf_q0) => heq.
  rewrite /I heq; smt.
 intros => h {h}.
 rewrite !group_pow_mult => h.
 cut: log (g ^ (r * m)) = log (g ^ (r * n)) by smt.
  rewrite !group_pow_log => {h} h. 
 cut: (r * m) / r = (r * n) / r by smt.
  rewrite (gf_q_mult_comm _ m) (gf_q_mult_comm _ n) /Prime_field.(/).
  by rewrite -!gf_q_mult_assoc !gf_q_mult_inv // !gf_q_mult_unit.
save.

lemma exp_rewr : forall X (m n : gf_q), X <> I => (X ^ m = X ^ n <=> m = n)  
 by (progress; apply (exp_inj X)).

lemma exp_inj2 : forall X Y (n : gf_q), n <> gf_q0 => X ^ n = Y ^ n => X = Y.
proof.
 intros => X Y n hn.
 cut [y ->]:= gen_def Y.
 cut [x ->]:= gen_def X.
 rewrite !group_pow_mult => h.
 cut := gen_exp_inj (x * n) (y * n) _ => // {h} h.
 cut: ( x * n * (inv n) = y * n * (inv n)) by smt => {h}.
 by rewrite -!gf_q_mult_assoc !gf_q_mult_inv // !gf_q_mult_unit.
save.

lemma exp_rewr2 : forall X Y (n : gf_q), n <> gf_q0 => X ^ n = Y ^ n <=> X = Y
by (progress; apply (exp_inj2 X Y n)).


lemma substr_inj : 
 forall (m n r : gf_q), m - r = n - r => m = n.
proof.
 intros => m n r h.
 cut: ((m - r) + r = (n - r) + r).
  by rewrite h.
 rewrite /Prime_field.(-) -!gf_q_add_assoc !(gf_q_add_comm (-r) r)  gf_q_add_minus.
 by rewrite (gf_q_add_comm m) (gf_q_add_comm n) !gf_q_add_unit.
save.
 
lemma log_prod_plus : forall (X Y : group), log (X * Y) = log X + log Y.
proof.
 intros => X Y.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 rewrite group_pow_add.
 by rewrite !group_pow_log.
save.

lemma log_div_minus : forall (X Y : group), log (X / Y) = log X - log Y.
proof.
 intros => X Y.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 by rewrite /Cyclic_group_prime.(/) !group_pow_log.
save.

lemma inv_inj : forall (X Y Z : group), X / Z = Y / Z => X = Y.
proof.
 intros X Y Z.
 rewrite /Cyclic_group_prime.(/) => h.
 cut:= gen_exp_inj (log X - log Z) (log Y - log Z) _ => // {h} h.
 cut: (log X = log Y).
  by apply (substr_inj _ _ (log Z)).
 intros => h'.
 cut: g ^ log X = g ^ log Y by rewrite h' //.
 by rewrite !group_log_pow.
save.

lemma inv_rewr : forall (X Y Z : group), X / Z = Y / Z <=> X = Y
 by (progress; apply (inv_inj _ _ Z)).

lemma div_cancel : forall (Y : group), Y / Y = g ^ gf_q0.
proof.
 intros => Y.
 by rewrite /Cyclic_group_prime.(/) /Prime_field.(-) gf_q_add_minus.
save.

lemma div_prod : forall (X Y : group), X / Y = X * (I / Y).
proof.
 rewrite /Cyclic_group_prime.(/) /I /Prime_field.(-) => X Y.
 cut:= gen_def X => [[x]] ->.
 by rewrite !group_pow_log group_pow_add gf_q_add_unit.
save.


lemma group_prod_assoc : forall (X Y Z : group), (X * Y) * Z = X * (Y * Z).
proof.
 intros => X Y Z.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 cut := gen_def Z => [[z]] ->.
 rewrite !group_pow_add.
 by rewrite gf_q_add_assoc.
save.

lemma prod_div : forall (X Y Z : group), X * (Y / Z) = (X * Y) / Z.
proof.
 intros => X Y Z.
 by rewrite div_prod -group_prod_assoc -div_prod.
save.

lemma I_prod_n : forall (X : group),  X * I = X.
proof.
 intros => X.
 cut := gen_def X => [[x]] ->.
 by rewrite /I group_pow_add gf_q_add_comm gf_q_add_unit.
save. 

lemma I_pow_n : forall n , I ^ n = I.
proof.
 intros => n; rewrite /I.
 by rewrite group_pow_mult gf_q_mult_comm gf_q_mult_zero. 
save.

lemma prod_comm : forall (X Y : group), X * Y = Y * X. 
proof.
 intros => X Y.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 by rewrite !group_pow_add gf_q_add_comm.
save.

lemma mult_div_I : forall (X : group), X / X = I.
 intros => X.
 cut := gen_def X => [[x]] ->.
 by rewrite /Cyclic_group_prime.(/) /Prime_field.(-) gf_q_add_minus /I.
save. 

lemma mult_div : forall (X Y : group), (X * Y) / Y = X.
proof.
 intros => X Y.
 by rewrite div_prod group_prod_assoc prod_div I_prod_n mult_div_I I_prod_n.
save.

lemma mult_pow_distr : forall (X Y : group) n, (X * Y) ^ n = X ^ n * Y ^ n.
proof.
 intros => X Y n.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 rewrite !group_pow_add !group_pow_mult group_pow_add.
 by rewrite gf_q_mult_comm gf_q_distr (gf_q_mult_comm x n) (gf_q_mult_comm y n).
save.

lemma div_pow_distr : forall (X Y : group) n, (X / Y) ^ n = X ^ n / Y ^ n.
proof.
 intros => X Y n.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 rewrite /Cyclic_group_prime.(/) !group_pow_mult !group_pow_log.
 rewrite /Prime_field.(-) gf_q_mult_comm gf_q_distr (gf_q_mult_comm x n). 
 by rewrite gf_q_mult_minus_right (gf_q_mult_comm y n).
save.

lemma pow_mult : forall (X : group) m n, X ^ m ^ n = X ^ (m * n). 
 intros => X m n.
 cut:= gen_def X => [[x]] ->.
 by rewrite !group_pow_mult gf_q_mult_assoc.
save.


lemma div_div_mult : forall (X Y Z : group), (X / Y) / Z = X / (Y * Z).
proof.
 intros => X Y Z.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 cut := gen_def Z => [[z]] ->.
 rewrite /Cyclic_group_prime.(/).
 rewrite log_div_minus log_prod_plus /Prime_field.(-).
 by rewrite neg_distr gf_q_add_assoc /Prime_field.(-).
save.

lemma pow_div_minus : forall (X : group) m n,  X ^ m / X ^ n = X ^ (m - n).
 intros => X m n.
 cut := gen_def X => [[x]] ->.
 rewrite /Cyclic_group_prime.(/).
 rewrite !group_pow_mult !group_pow_log.
 rewrite /Prime_field.(-) gf_q_distr gf_q_mult_comm (gf_q_mult_comm x n).
 by rewrite -gf_q_mult_minus (gf_q_mult_comm (-n) x).
save.

lemma log_pow_mult : forall (X : group) n, log (X ^ n) = n * log X.
proof.
 intros => X m.
 cut := gen_def X => [[x]] ->.
 by rewrite group_pow_mult !group_pow_log gf_q_mult_comm.
save.

lemma test_rewrite : forall Z_1 Z_2 Y (r s x1 x2 : gf_q),
s = r * x1 + x2 => 
Z_1 ^ r * Z_2 = Y ^ s <=>
(Z_1 / Y ^ x1) ^ r = (Y ^ x2) / Z_2.
proof.
 intros => Z_1 Z_2 Y r s x1 x2 ->.
 rewrite -(inv_rewr _ _ Z_2).
 rewrite mult_div.
 rewrite -(inv_rewr _ _ (Y ^ (x1 * r) )).
 cut -> : Z_1 ^ r / Y ^ (x1 * r) = (Z_1 / Y ^ x1) ^ r.
  by rewrite div_pow_distr pow_mult.
 cut -> : Y ^ (r * x1 + x2) / Z_2 / Y ^ (x1 * r) = Y ^ x2 / Z_2.
 rewrite div_div_mult prod_comm -div_div_mult pow_div_minus.
 cut: (r * x1 + x2 - x1 * r) = x2; last by smt.
 rewrite gf_q_add_comm /Prime_field.(-) -gf_q_add_assoc gf_q_mult_comm.
 by rewrite gf_q_add_minus gf_q_add_comm gf_q_add_unit.
 smt.
save. 

lemma div_eq_I : forall (X Y : group), I = X / Y  <=> X = Y.
proof.
 progress; last first.
 by rewrite /Cyclic_group_prime.(/) gf_q_minus /I.
 generalize H; rewrite /Cyclic_group_prime.(/) /I=> H.
 cut:= gen_exp_inj  gf_q0  (log X - log Y) _ => // {H} H.
 cut:= neg_zero (log X) (log Y) _ => // {H} H.
 by rewrite -(group_log_pow X) H group_log_pow.
save.
 
(* given two group elements, pick 3 group elements Z1, Z2 and Y *)
module type Pick = {
 fun pick (X1 : group, X2 : group) : group * group * group {*}
}.


module Trapdoor1( P : Pick) ={
 fun main () : bool = {
  var vX1, vZ1, vX2, vZ2, vY : group;
  var r, s : gf_q;
  vX1 = $dgroup;
  r = $dgf_q; (* except gf_q0 *)
  s = $dgf_q;
  vX2 = (g ^ s) / (vX1 ^ r);
  (vZ1, vZ2, vY) = P.pick(vX1, vX2);
  return (vZ1 = vY ^(log vX1) /\ vZ2 = vY ^(log vX2));
 }
}.


module Trapdoor2( P : Pick) ={
 fun main () : bool = {
  var vX1, vZ1, vX2, vZ2, vY : group;
  var r, s : gf_q;
  vX1 = $dgroup;
  r = $dgf_q;
  s = $dgf_q;
  vX2 = (g ^ s) / (vX1 ^ r);
  (vZ1, vZ2, vY) = P.pick(vX1, vX2);
  return ((vZ1 ^ r) * vZ2 = vY^s);
 }
}.

section.

declare module P : Pick.

axiom pick_ll : islossless P.pick.

local module G1 ( P : Pick) = {
 var bad : bool
 fun main () : bool = {
  var vX1, vZ1, vX2, vZ2, vY : group;
  var r, s : gf_q;
  bad = false;
  vX1 = $dgroup;
  r = $dgf_q;
  s = $dgf_q;
  vX2 = (g ^ s) / (vX1 ^ r);
  (vZ1, vZ2, vY) = P.pick(vX1, vX2);
  if (vZ1 <> (vY^ (log vX1)) /\ ((vZ1 / (vY^ (log vX1))) ^r = (vY^(log vX2)) / vZ2)) {
   bad = true;
  }
  return ((vZ1 / (vY^ (log vX1))) ^r = (vY^(log vX2)) / vZ2);
 }
}.


local equiv Eq1 : 
Trapdoor2(P).main ~ G1(P).main : true ==> ={res}.
proof.
 fun.
 wp.
 call (_ : true); wp.
 do!rnd; wp.
 skip; progress => //.
 cut ->:= test_rewrite x1 x2 x3 rL sL (log vX1L) (log (g ^ sL / vX1L ^ rL)) _ => //. 
 rewrite log_div_minus.
 rewrite group_pow_log.
 by rewrite log_pow_mult /Prime_field.(-) gf_q_add_comm -gf_q_add_assoc 
 -(gf_q_add_comm (rL * log vX1L))  gf_q_add_minus gf_q_add_comm gf_q_add_unit.
save.

local lemma Pr1 &m : 
Pr [Trapdoor2(P).main() @ &m : res] =
Pr [G1(P).main() @ &m : res]. 
proof.
 equiv_deno Eq1 => //.
save.

local equiv Eq2 :
Trapdoor1(P).main ~ G1(P).main : true ==> ! G1.bad{2} => ={res}.
proof.
 fun.
 wp; call (_ : true).
 wp.
 do!rnd; wp.
 skip; progress => //.
 cut: (x1 = x3 ^ log vX1L /\ x2 = x3 ^ log (g ^ sL / vX1L ^ rL) <=>
((x1 / x3 ^ log vX1L) ^ rL = x3 ^ log (g ^ sL / vX1L ^ rL) / x2)); last by smt.
 split.
 intros => [heq1 heq2].
 rewrite heq1 heq2 /Cyclic_group_prime.(/) !gf_q_minus group_pow_mult.
 by rewrite gf_q_mult_comm gf_q_mult_zero.
 intros heq.
 cut :( x1 = x3 ^ log vX1L \/
       ! (x1 / x3 ^ log vX1L) ^ rL = x3 ^ log (g ^ sL / vX1L ^ rL) / x2) by smt => {H8} H8.
 elim H8 => heq'.
 split => //.
 cut:  (! x2 = x3 ^ log (g ^ sL / vX1L ^ rL) => false); last by smt.
 intros => hneq; generalize heq => /=.
  rewrite heq' mult_div_I I_pow_n.
  rewrite div_eq_I.
 smt.
 smt.
save.

local lemma Pr2_aux &m : 
Pr [Trapdoor1(P).main() @ &m : res] <=
Pr [G1(P).main() @ &m : res] + Pr[G1(P).main() @ &m : G1.bad]. 
proof.
 apply (Real.Trans _ (Pr [G1(P).main() @ &m : res \/ G1.bad]) _).
 equiv_deno Eq2; smt.
 rewrite Pr mu_or; smt.
save.

local lemma Pr2 &m : 
Pr [Trapdoor1(P).main() @ &m : res] <=
Pr [Trapdoor2(P).main() @ &m : res] + Pr[G1(P).main() @ &m : G1.bad]. 
proof.
 rewrite (Pr1 &m).
 by apply (Pr2_aux &m).
save.

local module G2 ( P : Pick) = {
 var bad : bool
 fun main () : bool = {
  var vX1, vZ1, vX2, vZ2, vY : group;
  var r, s : gf_q;
  bad = false;
  vX1 = $dgroup;
  r = $dgf_q;
  s = $dgf_q;
  vX2 = $dgroup;
  (vZ1, vZ2, vY) = P.pick(vX1, vX2);
  if (vZ1 <> (vY^ (log vX1)) /\ ((vZ1 / (vY^ (log vX1))) ^r = (vY^(log vX2)) / vZ2)) {
   bad = true;
  }
  return ((vZ1 / (vY^ (log vX1))) ^r = (vY^(log vX2)) / vZ2);
 }
}.

local equiv Eq3 : 
G1(P).main ~ G2(P).main : true ==> G1.bad{1} = G2.bad{2}.
proof.
 fun.
 wp; call (_ : true).
 wp.
 rnd (lambda v, g ^ (v - log vX1{2} * r{2}))
     (lambda u, log u + r{2} * log vX1{2}).
 rnd{2}.
 rnd; rnd; wp; skip; progress => //; last 2 by smt.
 apply lossless. 
 by rewrite mu_x_def_in Dgroup.mu_x_def_in.
 by rewrite supp_def.
 rewrite group_pow_log /Prime_field.(-).
 rewrite -gf_q_add_assoc.
 by rewrite gf_q_mult_comm -(gf_q_add_comm  (rL * log vX1L)) gf_q_add_minus
            gf_q_add_comm gf_q_add_unit.
 by rewrite (gf_q_mult_comm rL) /Prime_field.(-) -gf_q_add_assoc gf_q_add_minus
             gf_q_add_comm gf_q_add_unit group_log_pow.
 by rewrite /Cyclic_group_prime.(/) group_pow_log log_pow_mult (gf_q_mult_comm rL).
save. 

local lemma Pr3_aux &m :
Pr[G1(P).main() @ &m : G1.bad] =
Pr[G2(P).main() @ &m : G2.bad]. 
proof.
 by equiv_deno Eq3.
save.

local lemma Pr3 &m : 
Pr [Trapdoor1(P).main() @ &m : res] <=
Pr [Trapdoor2(P).main() @ &m : res] + Pr[G2(P).main() @ &m : G2.bad]. 
proof.
 rewrite -(Pr3_aux &m).
 apply (Pr2 &m).
save.

local module G3 ( P : Pick) = {
 var bad : bool
 fun main () : bool = {
  var vX1, vZ1, vX2, vZ2, vY : group;
  var r, s : gf_q;
  bad = false;
  vX1 = $dgroup;
  vX2 = $dgroup;
  (vZ1, vZ2, vY) = P.pick(vX1, vX2);
  if (vZ1 <> (vY^ (log vX1))) {
   r = $dgf_q;
   s = $dgf_q;
   if (((vZ1 / (vY^ (log vX1))) ^r = (vY^(log vX2)) / vZ2)) {
    bad = true;
   }
  }
  return ((vZ1 / (vY^ (log vX1))) ^r = (vY^(log vX2)) / vZ2);
 }
}.


local equiv Eq4 : 
G2(P).main ~ G3(P).main : true ==> G2.bad{1} = G3.bad{2}.
proof.
 fun.
 swap{1} 3 3.
 swap{1} 3 3.
 seq 4 4: (={vX1, vX2, vZ1, vZ2, vY} /\ G2.bad{1} = G3.bad{2}).
 eqobs_in.
 if{2}.
 seq 2 2:
((={vX1, vX2, vZ1, vZ2, vY, r, s} /\ G2.bad{1} = G3.bad{2}) /\
  ! vZ1{2} = vY{2} ^ log vX1{2}).
 do 2! rnd; skip; progress => //.
 if{2}.
 rcondt{1} 1.
  by progress; skip; progress.
  by wp; skip.
 rcondf{1} 1.
  progress; skip; smt.
 by skip.
 rcondf{1} 3.
  by intros => &m; do 2!rnd; skip.
  do 2! rnd{1}; skip; progress.
  by apply lossless.
  by apply lossless.
save.

local lemma Pr4_aux &m :
Pr[G2(P).main() @ &m : G2.bad] =
Pr[G3(P).main() @ &m : G3.bad]. 
proof.
 by equiv_deno Eq4.
save.

local lemma Pr4 &m : 
Pr [Trapdoor1(P).main() @ &m : res] <=
Pr [Trapdoor2(P).main() @ &m : res] + Pr[G3(P).main() @ &m : G3.bad]. 
proof.
 rewrite -(Pr4_aux &m).
 apply (Pr3 &m).
save.

local module G4 ( P : Pick) = {
 var bad : bool
 fun main () : bool = {
  var vX1, vZ1, vX2, vZ2, vY, z : group;
  var r, s : gf_q;
  bad = false;
  vX1 = $dgroup;
  vX2 = $dgroup;
  (vZ1, vZ2, vY) = P.pick(vX1, vX2);
  if (vZ1 <> (vY^ (log vX1))) {
   r = $dgf_q;
   s = $dgf_q;
   z = $dgroup;
   if ((z = (vY^(log vX2)) / vZ2)) {
    bad = true;
   }
  }
  return ((vZ1 / (vY^ (log vX1))) ^r = (vY^(log vX2)) / vZ2);
 }
}.

require import Distr.


lemma log_inj : forall X Y, log X = log Y => X = Y.
proof.
 intros => X Y.
 cut:= gen_def X => [[x]] ->.
 cut:= gen_def Y => [[y]] ->.
 by rewrite !group_pow_log => ->.
save.

local equiv Eq5 : 
G3(P).main ~ G4(P).main : true ==> G3.bad{1} = G4.bad{2}.
proof.
 fun.
 seq 4 4: (={vX1, vX2, vZ1, vZ2, vY} /\ G3.bad{1} = G4.bad{2}).
  eqobs_in.
 if => //.
 seq 2 3: 
 (={vX1, vX2, vZ1, vZ2, vY} /\ G3.bad{1} = G4.bad{2} /\
  ! vZ1{1} = vY{1} ^ log vX1{1} /\ z{2} = (vZ1 / vY ^ log vX1){1} ^ r{1}).
 swap{2} 3 -1.
 rnd.
 rnd (lambda v, (vZ1 / vY ^ log vX1){2} ^ v)
     (lambda v, log v / ((log vZ1 - log ( vY ^ log vX1))){2}).
 rnd{2}.
 wp; skip.
 progress => //.
 apply lossless.
 by rewrite mu_x_def_in Dgroup.mu_x_def_in.
 by apply supp_def.
 rewrite  /Cyclic_group_prime.(/).
 rewrite log_pow_mult group_pow_log.
 rewrite /Prime_field.(/).
 rewrite -gf_q_mult_assoc.
 rewrite gf_q_mult_inv.
 cut: log vZ1{2} - log (vY{2} ^ log vX1{2}) = gf_q0 => vZ1{2} = vY{2} ^ log vX1{2}; last smt. 
 intros  => heq.
 cut := neg_zero (log vZ1{2}) (log (vY{2} ^ log vX1{2})) _.
  by rewrite heq.
 intros => {heq} heq.
 by apply log_inj.
 by rewrite gf_q_mult_unit.
 rewrite  /Cyclic_group_prime.(/) group_pow_mult.
 rewrite /Prime_field.(/).
 rewrite gf_q_mult_assoc. 
 rewrite gf_q_mult_comm. 
 rewrite gf_q_mult_assoc.
 rewrite (gf_q_mult_comm (inv (log vZ1{2} - log (vY{2} ^ log vX1{2})))).  
 rewrite gf_q_mult_inv.
 cut: log vZ1{2} - log (vY{2} ^ log vX1{2}) = gf_q0 => vZ1{2} = vY{2} ^ log vX1{2}; last smt. 
 intros  => heq.
 cut := neg_zero (log vZ1{2}) (log (vY{2} ^ log vX1{2})) _.
  by rewrite heq.
 intros => {heq} heq.
 by apply log_inj.
 rewrite gf_q_mult_comm gf_q_mult_unit.
 by rewrite group_log_pow.
 if.
 progress => //. 
 wp; skip; progress.
 wp; skip; progress.
save.

local lemma Pr5_aux &m :
Pr[G3(P).main() @ &m : G3.bad] =
Pr[G4(P).main() @ &m : G4.bad]. 
proof.
 by equiv_deno Eq5.
save.

local lemma Pr5 &m : 
Pr [Trapdoor1(P).main() @ &m : res] <=
Pr [Trapdoor2(P).main() @ &m : res] + Pr[G4(P).main() @ &m : G4.bad]. 
proof.
 rewrite -(Pr5_aux &m).
 apply (Pr4 &m).
save.


local module G5 ( P : Pick) = {
 fun main () : bool = {
  var vX1, vZ1, vX2, vZ2, vY, z : group;
  var r, s : gf_q;
  vX1 = $dgroup;
  vX2 = $dgroup;
  (vZ1, vZ2, vY) = P.pick(vX1, vX2);
  z = $dgroup;
  return ((z = (vY^(log vX2)) / vZ2));
 }
}.


local equiv Eq6 : 
G4(P).main ~ G5(P).main : true ==> G4.bad{1} => res{2}.
proof.
 fun.
 seq 4 3: (={vX1, vX2, vZ1, vZ2, vY} /\ G4.bad{1} = false).
 by call (_ : true); do 2! rnd; wp; skip; progress.
 if{1} => //; last by rnd{2}; skip; progress; apply Dgroup.lossless.
 wp; rnd; do 2! rnd{1}; skip; progress => //.
 apply lossless.
save.

local lemma Pr6_aux &m :
Pr[G4(P).main() @ &m : G4.bad] <=
Pr[G5(P).main() @ &m : res]. 
proof.
 by equiv_deno Eq6.
save.

local lemma Pr6_aux2 &m : Pr [G5(P).main() @ &m : res] = 1%r / q%r.
proof.
 bdhoare_deno (_ : true ==> res).
 fun.
 rnd.
 call (_ : true).
 apply pick_ll.
 do 2! rnd; skip; progress => //.
 cut -> : ((lambda (x : group),
     forall (result : group * group * group),
       let (vZ1, vZ2, vY) = result in
       mu dgroup (lambda (x0 : group), x0 = vY ^ log x / vZ2) = 1%r / q%r) = cpTrue).
 apply fun_ext; rewrite /Fun.(==) /cpTrue /=.
 progress.
 apply (_ : forall p, p => p = true);first smt.
 progress => //.
  rewrite -(Dgroup.mu_x_def_in ( x3 ^ log x / x2)) .
  rewrite /mu_x.
  apply Distr.mu_eq.
  rewrite /Fun.(==) => /= x'.
  smt.
  by rewrite -Dgroup.lossless /weight.
  by rewrite -Dgroup.lossless /weight.
  trivial.
  trivial.
save.

lemma Conclusion &m : 
Pr [Trapdoor1(P).main() @ &m : res] <=
Pr [Trapdoor2(P).main() @ &m : res] + 1%r / q%r. 
proof.
 rewrite -(Pr6_aux2 &m).
 apply (Real.Trans _ 
     (Pr[Trapdoor2(P).main() @ &m : res] + Pr[G4(P).main() @ &m : G4.bad]) _).
 apply (Pr5 &m).
 cut := Pr6_aux &m.
 smt.
save.

end section.
