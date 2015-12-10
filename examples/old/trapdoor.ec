require import Int.
require import FSet.
require import Bool.
require import Real.
require import AlgTactic.
require import Prime_field.
require import Cyclic_group_prime.
require import Option.

import Dgroup.
import Dgf_q.

(* reals axiom *)
(* we should be able to discharge this *)
axiom mult_pos_mon : forall (p q r : real), 0%r <= r => p <= q => r * p <= r * q.


(* group stuff *)
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
 move=> m n heq.
 cut: log (g ^ m) = log (g ^n).
  by rewrite heq.
 by rewrite !group_pow_log.
save.

lemma neg_distr : forall (x y : gf_q), -(x + y) = -x + -y.
proof.
 by move=> ? ?; fieldeq.
save.

lemma neg_zero : forall (x y : gf_q), gf_q0 = x - y => x = y.
proof.
 move=> ? ? ?.
 fieldeq; rewrite H; fieldeq.
save.

lemma gen_def : forall X, exists m, X = g ^ m. 
proof.
 move=> X; exists (log X).
 by rewrite group_log_pow.
save.

const I : group = g ^ gf_q0.

lemma exp_inj : forall X (m n : gf_q), X <> I => X ^ m = X ^ n => m = n.  
proof.
 move=> X m n.
 cut [r ->] := gen_def X.
 case (r = gf_q0) => heq.
  rewrite /I heq; smt.
 move=> h {h}.
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
 move=> X Y n hn.
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
 move=> m n r h.
 cut: ((m - r) + r = (n - r) + r).
  by rewrite h.
 rewrite /Prime_field.(-) -!gf_q_add_assoc !(gf_q_add_comm (-r) r)  gf_q_add_minus.
 by rewrite (gf_q_add_comm m) (gf_q_add_comm n) !gf_q_add_unit.
save.
 
lemma log_prod_plus : forall (X Y : group), log (X * Y) = log X + log Y.
proof.
 move=> X Y.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 rewrite group_pow_add.
 by rewrite !group_pow_log.
save.

lemma log_div_minus : forall (X Y : group), log (X / Y) = log X - log Y.
proof.
 move=> X Y.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 by rewrite -Cyclic_group_prime.div_def !group_pow_log.
save.

lemma inv_inj : forall (X Y Z : group), X / Z = Y / Z => X = Y.
proof.
 move=> X Y Z.
 rewrite -!Cyclic_group_prime.div_def => h.
 cut:= gen_exp_inj (log X - log Z) (log Y - log Z) _ => // {h} h.
 cut: (log X = log Y).
  by apply (substr_inj _ _ (log Z)).
 move=> h'.
 cut: g ^ log X = g ^ log Y by rewrite h' //.
 by rewrite !group_log_pow.
save.

lemma inv_rewr : forall (X Y Z : group), X / Z = Y / Z <=> X = Y
 by (progress; apply (inv_inj _ _ Z)).

lemma div_cancel : forall (Y : group), Y / Y = g ^ gf_q0.
proof.
 move=> Y.
 by rewrite -!Cyclic_group_prime.div_def /Prime_field.(-) gf_q_add_minus.
save.

lemma div_prod (X Y : group): X / Y = X * (I / Y).
proof.
 rewrite -!Cyclic_group_prime.div_def /I /Prime_field.(-).
 cut:= gen_def X => [[x]] ->.
 by rewrite !group_pow_log group_pow_add gf_q_add_unit.
save.


lemma group_prod_assoc : forall (X Y Z : group), (X * Y) * Z = X * (Y * Z).
proof.
 move=> X Y Z.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 cut := gen_def Z => [[z]] ->.
 rewrite !group_pow_add.
 by rewrite gf_q_add_assoc.
save.

lemma prod_div : forall (X Y Z : group), X * (Y / Z) = (X * Y) / Z.
proof.
 move=> X Y Z.
 by rewrite div_prod -group_prod_assoc -div_prod.
save.

lemma I_prod_n : forall (X : group),  X * I = X.
proof.
 move=> X.
 cut := gen_def X => [[x]] ->.
 by rewrite /I group_pow_add gf_q_add_comm gf_q_add_unit.
save. 

lemma I_pow_n : forall n , I ^ n = I.
proof.
 move=> n; rewrite /I.
 by rewrite group_pow_mult gf_q_mult_comm gf_q_mult_zero. 
save.

lemma prod_comm : forall (X Y : group), X * Y = Y * X. 
proof.
 move=> X Y.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 by rewrite !group_pow_add gf_q_add_comm.
save.

lemma mult_div_I : forall (X : group), X / X = I.
 move=> X.
 cut := gen_def X => [[x]] ->.
 by rewrite -!Cyclic_group_prime.div_def /Prime_field.(-) gf_q_add_minus /I.
save. 

lemma mult_div : forall (X Y : group), (X * Y) / Y = X.
proof.
 move=> X Y.
 by rewrite div_prod group_prod_assoc prod_div I_prod_n mult_div_I I_prod_n.
save.

lemma mult_pow_distr : forall (X Y : group) n, (X * Y) ^ n = X ^ n * Y ^ n.
proof.
 move=> X Y n.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 rewrite !group_pow_add !group_pow_mult group_pow_add.
 by rewrite gf_q_mult_comm gf_q_distr (gf_q_mult_comm x n) (gf_q_mult_comm y n).
save.

lemma div_pow_distr : forall (X Y : group) n, (X / Y) ^ n = X ^ n / Y ^ n.
proof.
 move=> X Y n.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 rewrite -!Cyclic_group_prime.div_def !group_pow_mult !group_pow_log.
 rewrite /Prime_field.(-) gf_q_mult_comm gf_q_distr (gf_q_mult_comm x n). 
 by rewrite gf_q_mult_minus_right (gf_q_mult_comm y n).
save.

lemma pow_mult : forall (X : group) m n, X ^ m ^ n = X ^ (m * n). 
 move=> X m n.
 cut:= gen_def X => [[x]] ->.
 by rewrite !group_pow_mult gf_q_mult_assoc.
save.


lemma div_div_mult : forall (X Y Z : group), (X / Y) / Z = X / (Y * Z).
proof.
 move=> X Y Z.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 cut := gen_def Z => [[z]] ->.
 rewrite -!Cyclic_group_prime.div_def.
 rewrite -log_div_minus log_prod_plus /Prime_field.(-).
 by rewrite neg_distr gf_q_add_assoc /Prime_field.(-); smt.
save.

lemma pow_div_minus : forall (X : group) m n,  X ^ m / X ^ n = X ^ (m - n).
 move=> X m n.
 cut := gen_def X => [[x]] ->.
 rewrite -!Cyclic_group_prime.div_def.
 rewrite !group_pow_mult !group_pow_log.
 rewrite /Prime_field.(-) gf_q_distr gf_q_mult_comm (gf_q_mult_comm x n).
 by rewrite -gf_q_mult_minus (gf_q_mult_comm (-n) x).
save.

lemma log_pow_mult : forall (X : group) n, log (X ^ n) = n * log X.
proof.
 move=> X m.
 cut := gen_def X => [[x]] ->.
 by rewrite group_pow_mult !group_pow_log gf_q_mult_comm.
save.

lemma test_rewrite : forall Z_1 Z_2 Y (r s x1 x2 : gf_q),
s = r * x1 + x2 => 
Z_1 ^ r * Z_2 = Y ^ s <=>
(Z_1 / Y ^ x1) ^ r = (Y ^ x2) / Z_2.
proof.
 move=> Z_1 Z_2 Y r s x1 x2 ->.
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
 by rewrite -!Cyclic_group_prime.div_def gf_q_minus /I.
 move: H; rewrite -!Cyclic_group_prime.div_def /I=> H.
 cut:= gen_exp_inj  gf_q0  (log X - log Y) _ => // {H} H.
 cut:= neg_zero (log X) (log Y) _ => // {H} H.
 by rewrite -(group_log_pow X) H group_log_pow.
save.
 

const qO : int. (* bound on calls *)
axiom qO_pos : 0 < qO.

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
 var bad_query : int option
 var bad_guess : int
 var gz1, gz2, gy : group
}.


module Trapdoor1( A : Adv) ={
  module TD : O ={
   fun check (Z1 Z2 Y : group) : bool ={
   var r : bool = false;
   if (M.cO < qO){
    r = (Z1 = Y ^(log M.gx1) /\ Z2 = Y ^(log M.gx2));
    M.cO = M.cO + 1;
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
  M.bad_query = None;
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
   M.cO = M.cO + 1;
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
  M.bad_query = None;
  b = AT.run(M.gx1, M.gx2);
  return b;
 }
}.

section.

declare module A : Adv {M}.

axiom run_ll : forall (O <: O{A}), islossless O.check => islossless A(O).run.

module G1( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO ){
    r = (Z1 / (Y^ (log M.gx1))) ^ M.r = (Y^(log M.gx2)) / Z2;
    M.cO = M.cO + 1;
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
  M.bad_query = None;
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
 move=> [heq1 heq2].
 rewrite heq1 heq2 -!Cyclic_group_prime.div_def !gf_q_minus group_pow_mult.
 by rewrite gf_q_mult_comm gf_q_mult_zero.
 move=> heq.
 cut :( Z1{2} = Y{2} ^ log M.gx1{2} \/
       ! (Z1{2} / Y{2} ^ log M.gx1{2}) ^ M.r{2} = Y{2} ^ log (g ^ M.s{2} / M.gx1{2} ^ M.r{2}) / Z2{2}) by smt.
 move=> H8.
 elim H8 => heq'.
 split => //.
 cut:  (! Z2{2} = Y{2} ^ log (g ^ M.s{2} / M.gx1{2} ^ M.r{2}) => false); last by smt.
 move=> hneq; move: heq => /=.
  rewrite heq' mult_div_I I_pow_n.
  rewrite div_eq_I.
 smt.
 smt.
 by move=> ? h; fun; wp.
 by move=> ?; fun; wp; skip.
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
    M.cO = M.cO + 1;
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
  M.bad_query = None;
  b = AT.run(M.gx1, M.gx2);
  return b;
 }
}.


local equiv Eq3 : 
G1(A).main ~ G2(A).main : true ==> M.bad{1} = M.bad{2}.
proof.
 fun.
 wp; call (_ : M.bad, 
              ={M.gx1, M.gx2, M.r, M.bad, M.cO}, 
              ={M.bad}).
 apply run_ll.
 fun; wp; skip; progress; smt.
 by move=> ? _; fun; wp; skip; progress; smt.
 by move=> ?; fun; wp; skip; progress; smt.
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
 by rewrite -!Cyclic_group_prime.div_def group_pow_log log_pow_mult (gf_q_mult_comm rL).
 by rewrite -!Cyclic_group_prime.div_def group_pow_log log_pow_mult (gf_q_mult_comm rL).
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

module G3( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO /\ ! M.bad){
   if (Z1 <> (Y^ (log M.gx1)) /\ ((Z1 / (Y^ (log M.gx1))) ^ M.r = (Y^(log M.gx2)) / Z2)) {
     M.bad = true;
    }
    r = (Z1 = Y ^ (log M.gx1) /\ Z2 = Y ^ (log M.gx2) );
    M.cO = M.cO + 1;
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
  M.bad_query = None;
  b = AT.run(M.gx1, M.gx2);
  return b;
 }
}.



local equiv Eq4 : 
G2(A).main ~ G3(A).main : true ==> M.bad{1} = M.bad{2}.
proof.
 fun.
 call (_ : M.bad, 
         ={M.gx1, M.gx2, M.r, M.bad, M.cO}, 
         ={M.bad}).
 apply run_ll.
 fun.
 wp; skip; progress.
 cut: ((Z1{2} / Y{2} ^ log M.gx1{2}) ^ M.r{2} = Y{2} ^ log M.gx2{2} / Z2{2}) <=>
(Z1{2} = Y{2} ^ log M.gx1{2} /\ Z2{2} = Y{2} ^ log M.gx2{2}); last by smt.
 split; last first.
 by move=> [-> ->]; rewrite !mult_div_I I_pow_n.
  move=> H'.
  cut :  Z1{2} = Y{2} ^ log M.gx1{2} \/
       (Z1{2} / Y{2} ^ log M.gx1{2}) ^ M.r{2} <> Y{2} ^ log M.gx2{2} / Z2{2}.
 smt.
 move=> {H2} [|] h.
 move: H'; rewrite h.
 rewrite !mult_div_I I_pow_n.
 progress => //.
 rewrite -I_prod_n H2 div_prod prod_comm group_prod_assoc (prod_comm _ Z2{2}).
 by rewrite -div_prod mult_div_I I_prod_n.
 smt.
 by move=> ? _; fun; wp; skip; progress; smt.
 by move=> ?; fun; wp; skip; progress; smt.
 by wp; do! rnd; skip; progress => //; smt.
save.


local lemma Pr4_aux &m :
Pr[G2(A).main() @ &m : M.bad] =
Pr[G3(A).main() @ &m : M.bad]. 
proof.
 by equiv_deno Eq4.
save.

local lemma Pr4 &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + Pr[G3(A).main() @ &m : M.bad]. 
proof.
 rewrite -(Pr4_aux &m).
 apply (Pr3 &m).
save.

module G4( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO /\ ! M.bad){
   if (Z1 <> (Y^ (log M.gx1)) /\ ((Z1 / (Y^ (log M.gx1))) ^ M.r = (Y^(log M.gx2)) / Z2)) {
     M.bad = true;
     M.bad_query = Some M.cO;
    }
    r = (Z1 = Y ^ (log M.gx1) /\ Z2 = Y ^ (log M.gx2) );
    M.cO = M.cO + 1;
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
  M.bad_query = None;
  b = AT.run(M.gx1, M.gx2);
  return b;
 }
}.

local equiv Eq5 : 
G3(A).main ~ G4(A).main : true ==> M.bad{1} <=> M.bad{2} /\ 0 <= proj M.bad_query{2} < qO.
proof.
 fun.
 call (_ : ={M.gx1, M.gx2, M.r, M.bad, M.cO} /\ 0 <= M.cO{2} <= qO /\ 
             (M.bad{2} => 0 <= proj M.bad_query{2} < M.cO{2} ) /\
             (! M.bad{2} =>  M.bad_query{2} = None ) ).
 fun; wp; skip; progress => //; smt.
 wp; do! rnd; skip; progress => //; smt.
save.

local lemma Pr5_aux &m :
Pr[G3(A).main() @ &m : M.bad] =
Pr[G4(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO]. 
proof.
 by equiv_deno Eq5.
save.

local lemma Pr5 &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + 
Pr [G4(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO]. 
proof.
 rewrite -(Pr5_aux &m).
 apply (Pr4 &m).
save.

module G5( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO /\ ! M.bad){
   if (Z1 <> (Y^ (log M.gx1)) /\ ((Z1 / (Y^ (log M.gx1))) ^ M.r = (Y^(log M.gx2)) / Z2)) {
     M.bad = true;
     M.bad_query = Some M.cO;
    }
    r = (Z1 = Y ^ (log M.gx1) /\ Z2 = Y ^ (log M.gx2) );
    M.cO = M.cO + 1;
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
  M.bad_query = None;
  b = AT.run(M.gx1, M.gx2);
  M.bad_guess = $[0 .. qO];
  return b;
 }
}.


local equiv Eq6: 
G4(A).main ~ G5(A).main : true ==> ={M.bad,M.bad_query}.
proof.
 fun.
 seq 8 8: (={M.bad,M.bad_query}).
 eqobs_in.
 rnd{2}; skip; progress.
 smt.
save.

local lemma Pr6_aux1 &m :
Pr[G4(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO] =
Pr[G5(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO].  
proof.
 by equiv_deno Eq6.
save.

local lemma Pr6_aux2 &m :
Pr[G5(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO] <=
qO%r * Pr[G5(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess].  
proof.
 admit. (* don't know how to prove this here. used to be "by compute" *)
save.


local lemma Pr6 &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + 
qO%r *Pr[G5(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess].  
proof.
 apply (Real.Trans _ 
     (Pr[Trapdoor2(A).main() @ &m : res] +
      Pr[G5(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO]) _).   
 rewrite -(Pr6_aux1 &m).
 apply (Pr5 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply (Pr6_aux2 &m).
save.

module G6( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO /\ ! M.bad){
   if (M.cO = M.bad_guess) {
     M.gz1 = Z1;
     M.gz2 = Z2; 
     M.gy = Y;
     if (M.gz1 <> (M.gy^ (log M.gx1)) /\ 
        ((M.gz1 / (M.gy^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2) ) {
         M.bad = true;
         M.bad_query = Some M.cO;
    }
   }
    r = (Z1 = Y ^ (log M.gx1) /\ Z2 = Y ^ (log M.gx2) );
    M.cO = M.cO + 1;
   }
   return r;
  }
 }
 module AT = A(TD)
 fun main () : bool = {
  var b : bool;
  M.gz1 = I;
  M.gz2 = I; 
  M.gy = I;
  M.gx1 = $dgroup;
  M.r = $dgf_q;
  M.s = $dgf_q;
  M.gx2 = $dgroup;
  M.bad = false; 
  M.cO = 0;
  M.bad_query = None;
  M.bad_guess = $[0 .. qO];
  b = AT.run(M.gx1, M.gx2);
  return b;
 }
}.

local equiv Eq7: 
G5(A).main ~ G6(A).main : true ==> (M.bad /\ proj M.bad_query = M.bad_guess){1} => 
                                   (M.bad /\ proj M.bad_query = M.bad_guess /\
 (M.gz1 <> (M.gy ^ (log M.gx1)) /\ 
         ((M.gz1 / (M.gy ^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2))){2}.
proof.
symmetry.
fun.
swap{2} 9 -1.
call (_ : M.bad /\ M.bad_query <> None /\ proj M.bad_query <> M.bad_guess,
          ={M.gx1, M.r, M.gx2, M.s, M.bad, M.bad_guess, M.bad_query, M.cO} /\ 
        ( M.bad{1} => (M.gz1 <> (M.gy ^ (log M.gx1)) /\ 
         ((M.gz1 / (M.gy ^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2)){1}) /\
       (M.bad_query{2} = None => M.bad_query{1} = None) /\ 
       ((M.bad_query{2} <> None /\ proj M.bad_query{2} = M.bad_guess{2}) => M.bad{1})).
apply run_ll.
fun.
seq 1 1 :
( ! (M.bad{2} /\ r{2} = false /\
     ! M.bad_query{2} = None /\ ! proj M.bad_query{2} = M.bad_guess{2}) /\
  ={Z1, Z2, Y, r} /\
  ={M.gx1, M.r, M.gx2, M.s, M.bad, M.bad_guess, M.bad_query, M.cO} /\
( M.bad{1} => (M.gz1 <> (M.gy ^ (log M.gx1)) /\ 
         ((M.gz1 / (M.gy ^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2)){1}) /\
   (M.bad_query{2} = None => M.bad_query{1} = None) /\
  ((M.bad_query{2} <> None /\ proj M.bad_query{2} = M.bad_guess{2}) => M.bad{1})).
wp; skip; progress.
if => //.
wp; skip; progress => //; smt.
move=> &2 h; fun; wp; skip; progress.
move=> &2; fun; wp; skip; progress;smt.
rnd; wp; do! rnd; wp; skip; progress; smt.
save.

local lemma Pr7_aux &m :
Pr[G5(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess] <=
Pr[G6(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess /\
(M.gz1 <> (M.gy ^ (log M.gx1)) /\ 
         ((M.gz1 / (M.gy ^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2))].  

proof.
 by equiv_deno Eq7.
save.


local lemma Pr7 &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + 
qO%r *Pr[G6(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess /\
(M.gz1 <> (M.gy ^ (log M.gx1)) /\ 
         ((M.gz1 / (M.gy ^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2))].  
proof.
apply (Real.Trans _ 
(Pr [Trapdoor2(A).main() @ &m : res] + 
qO%r *Pr[G5(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess]) _ ).  
apply (Pr6 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon; first smt.
 by apply (Pr7_aux &m).
save.

module G7( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO){
   if (M.cO = M.bad_guess) {
     M.gz1 = Z1;
     M.gz2 = Z2; 
     M.gy = Y;
   }
    r = (Z1 = Y ^ (log M.gx1) /\ Z2 = Y ^ (log M.gx2) );
    M.cO = M.cO + 1;
   }
   return r;
  }
 }
 module AT = A(TD)
 fun main () : bool = {
  var b : bool;
  M.gz1 = I;
  M.gz2 = I; 
  M.gy = I;
  M.gx1 = $dgroup;
  M.gx2 = $dgroup;
  M.bad = false; 
  M.cO = 0;
  M.bad_query = None;
  M.bad_guess = $[0 .. qO];
  b = AT.run(M.gx1, M.gx2);
  M.r = $dgf_q;
  M.s = $dgf_q;
  return (M.gz1 <> (M.gy^ (log M.gx1)) /\ 
        ((M.gz1 / (M.gy^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2) );
 }
}.

local equiv Eq8: 
G6(A).main ~ G7(A).main : true ==> 
           (M.bad /\ proj M.bad_query = M.bad_guess /\
           (M.gz1 <> (M.gy ^ (log M.gx1)) /\ 
           ((M.gz1 / (M.gy ^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2))){1} =>
           res{2}.
proof.
symmetry.
fun.
swap{1} 11 -6.
swap{1} 12 -6.
call (_ : M.bad,
          ={M.gx1, M.r, M.gx2, M.s, M.cO, M.bad, M.bad_guess} /\
           !M.bad{1} /\
          (M.bad{2} => (M.gz1 <> (M.gy ^ (log M.gx1)) /\ 
           ((M.gz1 / (M.gy ^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2)){2} /\
            ={M.gy, M.gz1, M.gz2}),
          ={M.gx1, M.r, M.gx2, M.s, M.gy, M.gz1, M.gz2} /\
           (M.gz1 <> (M.gy ^ (log M.gx1)) /\ 
           ((M.gz1 / (M.gy ^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2)){2} /\ 
            M.bad_guess{1} < M.cO{1} ).
apply run_ll.
fun.
wp; skip; progress => //; smt.
move=> &2 _; fun; wp; skip; progress => //; smt.
move=> ?; fun; wp; skip; progress => //; smt.
rnd; wp; do !rnd; wp; skip; progress => //; smt.
save.

local lemma Pr8_aux &m :
Pr[G6(A).main() @ &m : (M.bad /\ proj M.bad_query = M.bad_guess /\
           (M.gz1 <> (M.gy ^ (log M.gx1)) /\ 
           ((M.gz1 / (M.gy ^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2)))] <=
Pr[G7(A).main() @ &m : res].  
proof.
 by equiv_deno Eq8.
save.


local lemma Pr8 &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + 
qO%r *Pr[G7(A).main() @ &m : res].  
proof.
apply (Real.Trans _ 
(Pr [Trapdoor2(A).main() @ &m : res] + 
qO%r * Pr[G6(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess /\
(M.gz1 <> (M.gy ^ (log M.gx1)) /\ 
         ((M.gz1 / (M.gy ^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2))]) _ ).  
apply (Pr7 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon; first smt. 
 by apply (Pr8_aux &m).
save.

module G8( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO){
   if (M.cO = M.bad_guess) {
     M.gz1 = Z1;
     M.gz2 = Z2; 
     M.gy = Y;
   }
    r = (Z1 = Y ^ (log M.gx1) /\ Z2 = Y ^ (log M.gx2) );
    M.cO = M.cO + 1;
   }
   return r;
  }
 }
 module AT = A(TD)
 fun main () : bool = {
  var b : bool;
  var ret : bool;
  M.gz1 = I;
  M.gz2 = I; 
  M.gy = I;
  M.gx1 = $dgroup;
  M.gx2 = $dgroup;
  M.bad = false; 
  M.cO = 0;
  M.bad_query = None;
  M.bad_guess = $[0 .. qO];
  b = AT.run(M.gx1, M.gx2);
  ret = false;
  if (M.gz1 <> (M.gy^ (log M.gx1))) {
    M.r = $dgf_q;
    ret = (M.gz1 / (M.gy^ (log M.gx1))) ^ M.r = (M.gy^(log M.gx2)) / M.gz2;
  }
  return (ret);
 }
}.


local equiv Eq9: 
G7(A).main ~ G8(A).main : true ==> res{1} = res{2}. 
proof.
fun.
seq 10 10: (={M.gx1, M.gx2, M.gy, M.gz1, M.gz2}).
eqobs_in.
sp.
if{2}.
wp.
rnd{1}; rnd.
skip; progress => //; smt.
do! rnd{1}; skip; progress => //; smt.
save.

local lemma Pr9 &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + 
qO%r *Pr[G8(A).main() @ &m : res].  
proof.
 rewrite -(_ : Pr[G7(A).main() @ &m : res] = Pr[G8(A).main() @ &m : res]).
  by equiv_deno Eq9.
  by apply (Pr8 &m).
save. 

module G9( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO){
   if (M.cO = M.bad_guess) {
     M.gz1 = Z1;
     M.gz2 = Z2; 
     M.gy = Y;
   }
    r = (Z1 = Y ^ (log M.gx1) /\ Z2 = Y ^ (log M.gx2) );
    M.cO = M.cO + 1;
   }
   return r;
  }
 }
 module AT = A(TD)
 fun main () : bool = {
  var b : bool;
  var ret : bool;
  var gw : group;
  M.gz1 = I;
  M.gz2 = I; 
  M.gy = I;
  M.gx1 = $dgroup;
  M.gx2 = $dgroup;
  M.bad = false; 
  M.cO = 0;
  M.bad_query = None;
  M.bad_guess = $[0 .. qO];
  b = AT.run(M.gx1, M.gx2);
  ret = false;
  if (M.gz1 <> (M.gy^ (log M.gx1))) {
    gw = $dgroup;
    ret = gw = (M.gy^(log M.gx2)) / M.gz2;
  }
  return (ret);
 }
}.

local equiv Eq10: 
G8(A).main ~ G9(A).main : true ==> res{1} = res{2}. 
proof.
 fun.
 seq 11 11: (={M.gx1, M.gx2, M.gy, M.gz1, M.gz2, ret}).
  by eqobs_in.
  if => //.
 wp.
 rnd (lambda v, (M.gz1 / M.gy ^ log M.gx1){2} ^ v)
     (lambda v, log v / ((log M.gz1 - log ( M.gy ^ log M.gx1))){2}).
 skip; progress => //.
 by rewrite mu_x_def_in Dgroup.mu_x_def_in.
 by apply supp_def.
 rewrite -!Cyclic_group_prime.div_def.
 rewrite log_pow_mult group_pow_log.
 rewrite /Prime_field.(/).
 rewrite -gf_q_mult_assoc.
 rewrite gf_q_mult_inv.
 cut: log M.gz1{2} - log (M.gy{2} ^ log M.gx1{2}) = gf_q0 => M.gz1{2} = M.gy{2} ^ log M.gx1{2}; last smt. 
 move=> heq.
 cut := neg_zero (log M.gz1{2}) (log (M.gy{2} ^ log M.gx1{2})) _.
  by rewrite heq.
 move=> {heq} heq.
 apply (_ : forall V W, log V = log W => V = W) => //.
  by move=> V W h; rewrite -group_log_pow -(group_log_pow W) h.
 by rewrite gf_q_mult_unit.
 rewrite -!Cyclic_group_prime.div_def group_pow_mult.
 rewrite /Prime_field.(/).
 rewrite gf_q_mult_assoc. 
 rewrite gf_q_mult_comm. 
 rewrite gf_q_mult_assoc.
 rewrite (gf_q_mult_comm (inv (log M.gz1{2} - log (M.gy{2} ^ log M.gx1{2})))).  
 rewrite gf_q_mult_inv.
 cut: log M.gz1{2} - log (M.gy{2} ^ log M.gx1{2}) = gf_q0 =>
       M.gz1{2} = M.gy{2} ^ log M.gx1{2}; last smt. 
 move=> heq.
 cut := neg_zero (log M.gz1{2}) (log (M.gy{2} ^ log M.gx1{2})) _.
  by rewrite heq.
 move=> {heq} heq.
 apply (_ : forall V W, log V = log W => V = W) => //.
  by move=> V W h; rewrite -group_log_pow -(group_log_pow W) h.
 rewrite gf_q_mult_comm gf_q_mult_unit.
 by rewrite group_log_pow.
save.


local lemma Pr10 &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + 
qO%r *Pr[G9(A).main() @ &m : res].  
proof.
 rewrite -(_ : Pr[G8(A).main() @ &m : res] = Pr[G9(A).main() @ &m : res]).
  by equiv_deno Eq10.
  by apply (Pr9 &m).
save. 

module G10( A : Adv) ={
 module TD : O ={
  fun check (Z1 Z2 Y : group) : bool ={
  var r : bool = false;
  if (M.cO < qO){
   if (M.cO = M.bad_guess) {
     M.gz1 = Z1;
     M.gz2 = Z2; 
     M.gy = Y;
   }
    r = (Z1 = Y ^ (log M.gx1) /\ Z2 = Y ^ (log M.gx2) );
    M.cO = M.cO + 1;
   }
   return r;
  }
 }
 module AT = A(TD)
 fun main () : bool = {
  var b : bool;
  var ret : bool;
  var gw : group;
  M.gz1 = I;
  M.gz2 = I; 
  M.gy = I;
  M.gx1 = $dgroup;
  M.gx2 = $dgroup;
  M.bad = false; 
  M.cO = 0;
  M.bad_query = None;
  M.bad_guess = $[0 .. qO];
  b = AT.run(M.gx1, M.gx2);
  ret = false;
  gw = $dgroup;
  return ((gw = (M.gy^(log M.gx2)) / M.gz2));
 }
}.

local equiv Eq11: 
G9(A).main ~ G10(A).main : true ==> res{1} => res{2}. 
proof.
fun.
seq 10 10: (={M.gx1, M.gx2, M.gy, M.gz1, M.gz2}).
eqobs_in.
sp.
if{1}.
wp.
rnd.
skip; progress => //; smt.
do! rnd{2}; skip; progress => //; smt.
save.


local lemma Pr11_aux &m :
Pr[G10(A).main() @ &m : res] = 1%r / q%r.
proof.
 bdhoare_deno (_ : true ==> res) => //.
 fun; rnd; wp.
 call (_ : true) => //.
  by apply run_ll.
  by fun; wp.
 rnd; wp; do !rnd; wp; skip; progress.
 apply (_ :forall p, Fun.(==) p  Fun.cpTrue => mu dgroup p = 1%r).
 rewrite -Dgroup.lossless /Distr.weight => //=; smt.
 rewrite /Fun.(==) /Fun.cpTrue /= => x.
 apply (_ : forall p, p => p = true);first smt.
 split; last smt.
 move=> gz2 gy; move: ( gy ^ log x / gz2) => y.
 rewrite -(Dgroup.mu_x_def_in y) /Distr.mu_x.
 apply Distr.mu_eq; rewrite /Fun.(==) /= => x'; smt.
 by rewrite -Dgroup.lossless /Distr.weight.
save.

lemma Conclusion &m : 
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + 
qO%r * (1%r / q%r).  
proof.
 rewrite -(Pr11_aux &m).
 apply ( Real.Trans _ 
       (Pr[Trapdoor2(A).main() @ &m : res] + qO%r * Pr[G9(A).main() @ &m : res]) _).
 apply (Pr10 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon; first smt. 
 by equiv_deno Eq11. 
save. 

end section.

print axiom Conclusion.