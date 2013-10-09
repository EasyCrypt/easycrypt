require import Int.
require import FSet.
require import Bool.
require import Real.
require import AlgTactic.
require import Prime_field.
require import Cyclic_group_prime.

import Dgroup.
import Dgf_q.

type zq = gf_q.

op pow : zq -> int -> zq.
op (^^) = pow.

axiom qf_expr0 : forall (x : zq), x^^0 = gf_q1.
axiom qf_exprS : forall (x : zq) i, 0 <= i => x^^(i+1) = x * x^^i.
axiom qf_exprN : forall (x : zq) i, 0 <= i => x^^(-i) = inv (x^^i).


op ofint : int -> zq.

axiom qf_ofint0 : ofint 0 = Prime_field.gf_q0.
axiom qf_ofint1 : ofint 1 = Prime_field.gf_q1.
axiom qf_ofintS : forall i, 0 <= i => ofint (i+1) = ofint i + gf_q1.
axiom qf_ofintN : forall (i : int), ofint (-i) = -(ofint i).

instance field with zq
  op rzero = Prime_field.gf_q0
  op rone  = Prime_field.gf_q1
  op add   = Prime_field.( + )
  op opp   = Prime_field.([-])
  op mul   = Prime_field.( * )
  op expr  = pow
  op sub   = Prime_field.( - )
  op ofint = ofint
  op inv   = Prime_field.inv
  op div   = Prime_field.(/)

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof mulrV     by smt
  proof expr0     by smt
  proof exprS     by smt
  proof exprN     by smt
  proof subrE     by smt
  proof divrE     by smt
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt
  proof ofintN    by smt.


(* lemmas of groups and prime field *)
lemma gen_exp_inj : forall(m n : gf_q), g ^ m = g ^ n => m = n.
proof.
 intros => m n heq.
 cut: log (g ^ m) = log (g ^n).
  by rewrite heq.
 by rewrite !group_pow_log.
save.

lemma neg_distr : forall (x y : gf_q), -(x + y) = -x + -y.
proof.
 by intros => ? ?; fieldeq.
save.

lemma neg_zero : forall (x y : gf_q), gf_q0 = x - y => x = y.
proof.
 intros => ? ? ?.
 fieldeq; rewrite H; fieldeq.
save.

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
 

const qO : int. (* bound on calls *)

module type O = {
 fun check (Z1 Z2 Y : group) : bool
}.

module type Adv (O : O) = {
 fun run (X1 : group, X2 : group) : bool {* O.check}
}.

module M = {
 var r, s : gf_q
 var gx1, gx2 : group
 var bad : bool
 var cO : int
}.


module Trapdoor1( A : Adv) ={
  module TD : O ={
   fun check (Z1 Z2 Y : group) : bool ={
   var r : bool = false;
   if (M.cO < qO){
    r = (Z1 = Y ^(log M.gx1) /\ Z2 = Y ^(log M.gx2));
   }
   return r;
   }
 }
 module AT = A(TD)
 fun main () : bool = {
  var b : bool;
  M.gx1 = $dgroup;
  M.r = $dgf_q;
  M.s = $dgf_q;
  M.gx2 = (g ^ M.s) / (M.gx1 ^ M.r);
  M.cO = 0;
  b = AT.run(M.gx1, M.gx2);
  return b;
 }
}.

module Trapdoor2( A : Adv) ={
 module TD : O = {
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO){
   r = ((Z1 ^ M.r) * Z2 = Y ^ M.s);
   }
  return r ;
  }
 }
 module AT = A(TD)
 fun main () : bool = {
  var b : bool;
  M.gx1 = $dgroup;
  M.r = $dgf_q;
  M.s = $dgf_q;
  M.gx2 = (g ^ M.s) / (M.gx1 ^ M.r);
  M.cO = 0;
  b = AT.run(M.gx1, M.gx2);
  return b;
 }
}.

(* module Trapdoor2( P : Pick) ={ *)
(*  fun main () : bool = { *)
(*   var vX1, vZ1, vX2, vZ2, vY : group; *)
(*   var r, s : gf_q; *)
(*   vX1 = $dgroup; *)
(*   r = $dgf_q; *)
(*   s = $dgf_q; *)
(*   vX2 = (g ^ s) / (vX1 ^ r); *)
(*   (vZ1, vZ2, vY) = P.pick(vX1, vX2); *)
(*   return ((vZ1 ^ r) * vZ2 = vY^s); *)
(*  } *)
(* }. *)

section.

declare module A : Adv {M}.

axiom run_ll : forall (O <: O{A}), islossless O.check => islossless A(O).run.

module G1( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO ){
    r = (Z1 / (Y^ (log M.gx1))) ^ M.r = (Y^(log M.gx2)) / Z2;
    if (Z1 <> (Y^ (log M.gx1)) /\ ((Z1 / (Y^ (log M.gx1))) ^ M.r = (Y^(log M.gx2)) / Z2)) {
     M.bad = true;
    }
   }
     return r;
  }
 }
 module AT = A(TD)
 fun main () : bool = {
  var b : bool;
  M.gx1 = $dgroup;
  M.r = $dgf_q;
  M.s = $dgf_q;
  M.gx2 = (g ^ M.s) / (M.gx1 ^ M.r);
  M.bad = false;
  M.cO = 0;
  b = AT.run(M.gx1, M.gx2);
  return b;
 }
}.

local equiv Eq1 : 
Trapdoor2(A).main ~ G1(A).main : true ==> ={res}.
proof.
 fun.
 call (_ : ={M.gx1, M.gx2, M.r, M.s, M.cO} /\ (M.gx2 = g ^ M.s / M.gx1 ^ M.r){2}).
 fun; wp; skip; progress.
 cut ->:= test_rewrite Z1{2} Z2{2} Y{2} M.r{2} M.s{2} (log M.gx1{2}) (log (g ^ M.s{2} / M.gx1{2} ^ M.r{2})) _ => //. 
 rewrite log_div_minus.
 rewrite group_pow_log.
 by rewrite log_pow_mult /Prime_field.(-) gf_q_add_comm -gf_q_add_assoc 
 -(gf_q_add_comm (M.r{2} * log M.gx1{2}))  gf_q_add_minus gf_q_add_comm gf_q_add_unit.
 wp; do 3! rnd; skip; progress => //.
save.

local lemma Pr1 &m : 
Pr [Trapdoor2(A).main() @ &m : res] =
Pr [G1(A).main() @ &m : res]. 
proof.
 equiv_deno Eq1 => //.
save.

local equiv Eq2 :
Trapdoor1(A).main ~ G1(A).main : true ==> ! M.bad{2} => ={res}.
proof.
 fun.
 call (_ : M.bad, 
          ={M.gx1, M.gx2, M.r, M.s, M.cO} /\ (M.gx2 = g ^ M.s / M.gx1 ^ M.r){2}) => //.
 apply run_ll. 
 fun; wp; skip; progress => //.
 cut: (Z1{2} = Y{2} ^ log M.gx1{2} /\ Z2{2} = Y{2} ^ log (g ^ M.s{2} / M.gx1{2} ^ M.r{2}) <=>
((Z1{2} / Y{2} ^ log M.gx1{2}) ^ M.r{2} = Y{2} ^ log (g ^ M.s{2} / M.gx1{2} ^ M.r{2}) / Z2{2})); last by smt.
 split.
 intros => [heq1 heq2].
 rewrite heq1 heq2 /Cyclic_group_prime.(/) !gf_q_minus group_pow_mult.
 by rewrite gf_q_mult_comm gf_q_mult_zero.
 intros heq.
 cut :( Z1{2} = Y{2} ^ log M.gx1{2} \/
       ! (Z1{2} / Y{2} ^ log M.gx1{2}) ^ M.r{2} = Y{2} ^ log (g ^ M.s{2} / M.gx1{2} ^ M.r{2}) / Z2{2}) by smt.
 intros H8.
 elim H8 => heq'.
 split => //.
 cut:  (! Z2{2} = Y{2} ^ log (g ^ M.s{2} / M.gx1{2} ^ M.r{2}) => false); last by smt.
 intros => hneq; generalize heq => /=.
  rewrite heq' mult_div_I I_pow_n.
  rewrite div_eq_I.
 smt.
 smt.
 by intros => ? h; fun; wp.
 by intros => ?; fun; wp; skip.
 wp; do 3! rnd; skip; progress; smt.
save.

local lemma Pr2_aux &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [G1(A).main() @ &m : res] + Pr[G1(A).main() @ &m : M.bad]. 
proof.
 apply (Real.Trans _ (Pr [G1(A).main() @ &m : res \/ M.bad]) _).
 equiv_deno Eq2; smt.
 rewrite Pr mu_or; smt.
save.

local lemma Pr2 &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + Pr[G1(A).main() @ &m : M.bad]. 
proof.
 rewrite (Pr1 &m).
 by apply (Pr2_aux &m).
save.

module G2( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO /\ ! M.bad){
   if (Z1 <> (Y^ (log M.gx1)) /\ ((Z1 / (Y^ (log M.gx1))) ^ M.r = (Y^(log M.gx2)) / Z2)) {
     M.bad = true;
    }
    r = ((Z1 / (Y^ (log M.gx1))) ^ M.r = (Y^(log M.gx2)) / Z2);
   }
   return r;
  }
 }
 module AT = A(TD)
 fun main () : bool = {
  var b : bool;
  M.gx1 = $dgroup;
  M.r = $dgf_q;
  M.s = $dgf_q;
  M.gx2 = $dgroup;
  M.bad = false; 
  M.cO = 0;
  b = AT.run(M.gx1, M.gx2);
  return b;
 }
}.

(* local module G2 ( P : Pick) = { *)
(*  var bad : bool *)
(*  fun main () : bool = { *)
(*   var vX1, vZ1, vX2, vZ2, vY : group; *)
(*   var r, s : gf_q; *)
(*   bad = false; *)
(*   vX1 = $dgroup; *)
(*   r = $dgf_q; *)
(*   s = $dgf_q; *)
(*   vX2 = $dgroup; *)
(*   (vZ1, vZ2, vY) = P.pick(vX1, vX2); *)
(*   if (vZ1 <> (vY^ (log vX1)) /\ ((vZ1 / (vY^ (log vX1))) ^r = (vY^(log vX2)) / vZ2)) { *)
(*    bad = true; *)
(*   } *)
(*   return ((vZ1 / (vY^ (log vX1))) ^r = (vY^(log vX2)) / vZ2); *)
(*  } *)
(*} . *)

local equiv Eq3 : 
G1(A).main ~ G2(A).main : true ==> M.bad{1} = M.bad{2}.
proof.
 fun.
 wp; call (_ : M.bad, 
              ={M.gx1, M.gx2, M.r, M.bad, M.cO}, 
              ={M.bad}).
 apply run_ll.
 fun; wp; skip; progress; smt.
 by intros => ? _; fun; wp; skip; progress; smt.
 by intros => ?; fun; wp; skip; progress; smt.
 wp.
 rnd (lambda v, g ^ (v - log M.gx1{2} * M.r{2}))
     (lambda u, log u + M.r{2} * log M.gx1{2}).
 rnd{2}.
 rnd; rnd; wp; skip; progress => //.
 apply lossless. 
 by rewrite mu_x_def_in Dgroup.mu_x_def_in.
 by rewrite supp_def.
 rewrite group_pow_log /Prime_field.(-).
 rewrite -gf_q_add_assoc.
 by rewrite gf_q_mult_comm -(gf_q_add_comm  (rL * log gx1L)) gf_q_add_minus
            gf_q_add_comm gf_q_add_unit.
 by rewrite (gf_q_mult_comm rL) /Prime_field.(-) -gf_q_add_assoc gf_q_add_minus
             gf_q_add_comm gf_q_add_unit group_log_pow.
 by rewrite /Cyclic_group_prime.(/) group_pow_log log_pow_mult (gf_q_mult_comm rL).
 by rewrite /Cyclic_group_prime.(/) group_pow_log log_pow_mult (gf_q_mult_comm rL).
 smt.
save. 

local lemma Pr3_aux &m :
Pr[G1(A).main() @ &m : M.bad] =
Pr[G2(A).main() @ &m : M.bad]. 
proof.
 by equiv_deno Eq3.
save.

local lemma Pr3 &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + Pr[G2(A).main() @ &m : M.bad]. 
proof.
 rewrite -(Pr3_aux &m).
 apply (Pr2 &m).
save.
