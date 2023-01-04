require import Int.
require import FSet.
require import Bool.
require import List.
require import Real.
require import StdOrder.
(*****) import RealOrder.
require import AlgTactic.

require (****) Group.

clone Group.CyclicGroup as G.

axiom prime_p : IntDiv.prime G.order.

clone G.PowZMod as GP with
  lemma prime_order <- prime_p.

clone GP.FDistr as FD.

clone GP.ZModE.ZModpField as ZPF.

import G GP FD GP.ZModE.

(* reals axiom *)
(* we should be able to discharge this *)
lemma mult_pos_mon : forall (p q r : real), 0%r <= r => p <= q => r * p <= r * q
  by smt(ler_pmul2l).

(* lemmas of groups and prime field *)
lemma gen_exp_inj (m n : exp) : g ^ m = g ^ n => m = n
  by move => mnP; rewrite log_bij in mnP; move: mnP; rewrite !loggK.

lemma neg_distr (x y : exp) : -(x + y) = -x + -y
  by rewrite ZPF.opprD.

lemma neg_zero (x y : exp) : zero = x - y => x = y
  by rewrite -ZPF.subr_eq ZPF.sub0r ZPF.opprK.

lemma gen_def (x : group) : exists (m : exp), x = g ^ m by smt(expgK).

const i : group = g ^ zero.

lemma exp_inj x (m n : exp) : x <> i => x ^ m = x ^ n => m = n.
proof.
move => xP mnP; have logP: loge (x ^ m) = loge (x ^ n) by smt().
have {logP} : (m - n) * loge x = zero
  by move: logP; rewrite !logrzM ZPF.mulrBl => ->; algebra.
by rewrite ZPF.mulf_eq0 ZPF.subr_eq0; smt(log_bij loggK).
qed.

lemma exp_rewr x (m n : exp) : x <> i => (x ^ m = x ^ n <=> m = n)
  by smt(exp_inj).

lemma exp_inj2 x y (n : exp) : n <> zero => x ^ n = y ^ n => x = y.
proof.
move => nP xyP; have: loge (x ^ n) = loge (y ^ n) by smt().
rewrite !logrzM -ZPF.subr_eq0 -ZPF.mulrBr.
rewrite ZPF.mulf_eq0 ZPF.subr_eq0.
by smt(log_bij).
qed.

lemma exp_rewr2 x y (n : exp) : n <> zero => x ^ n = y ^ n <=> x = y
  by smt(exp_inj2).

lemma substr_inj (m n r : exp) : m - r = n - r => m = n
  by apply ZPF.addIr.

lemma log_prod_plus (x y : group) : loge (x * y) = loge x + loge y
  by rewrite logDr.

lemma log_div_minus (x y : group) : loge (x / y) = loge x - loge y
  by rewrite logDrN.

lemma inv_inj (x y z : group) : x / z = y / z => x = y by apply mulIc.

lemma inv_rewr (x y z : group) : x / z = y / z <=> x = y by smt(inv_inj).

lemma div_cancel (y : group) : y / y = g ^ GP.ZModE.zero
  by rewrite -expgK -expB ZPF.subrr.

lemma div_prod (x y : group) : x / y = x * (i / y)
  by rewrite -(expgK y) /i -expB ZPF.add0r -logrV !expgK.

lemma group_prod_assoc (x y z : group) : (x * y) * z = x * (y * z)
  by rewrite mulcA.

lemma prod_div (x y z : group) : x * (y / z) = (x * y) / z
  by rewrite mulcA.

lemma I_prod_n (x : group) : x * i = x
  by rewrite -expgK /i -expD ZPF.addr0.

lemma I_pow_n (n : exp) : i ^ n = i
  by rewrite -expM ZPF.mul0r.

lemma prod_comm (x y : group) : x * y = y * x by rewrite mulcC.

lemma mult_div_I (x : group) : x / x = i
  by rewrite -expgK -expB ZPF.subrr.

lemma mult_div (x y : group) : (x * y) / y = x
  by rewrite -mulcA mult_div_I I_prod_n.

lemma mult_pow_distr (x y : group) (n : exp) : (x * y) ^ n = x ^ n * y ^ n.
proof.
have := gen_def x => [[xe]] ->.
have := gen_def y => [[ye]] ->.
by rewrite -!expM -!expD -ZPF.mulrDl expM.
qed.

lemma div_pow_distr (x y : group) (n : exp) : (x / y) ^ n = x ^ n / y ^ n.
proof.
rewrite mult_pow_distr -expN; congr.
suff: inv y ^ n * y ^ n = (y ^ -n) * y ^ n by apply mulIc.
rewrite -mult_pow_distr mulVc -expD ZPF.addrC.
rewrite ZPF.subrr exp0 -(exp0 g) -expM.
by rewrite ZPF.mul0r.
qed.

lemma pow_mult (x : group) (m n : exp) : x ^ m ^ n = x ^ (m * n) by rewrite expM.

lemma div_div_mult (x y z : group) : (x / y) / z = x / (y * z)
  by rewrite invM_com (mulcC (inv z)) mulcA.

lemma pow_div_minus (x : group) (m n : exp) : x ^ m / x ^ n = x ^ (m - n)
  by rewrite expB.

lemma log_pow_mult (x : group) (n : exp) : loge (x ^ n) = n * loge x
  by rewrite logrzM.

lemma test_rewrite (y z1 z2 : group) (r s x1 x2 : exp) :
  s = r * x1 + x2 =>
  z1 ^ r * z2 = y ^ s <=> (z1 / y ^ x1) ^ r = (y ^ x2) / z2.
proof.
move => ->; rewrite -(inv_rewr _ _ z2) -mulcA mulcV mulc1 expD.
rewrite ZPF.mulrC expM -(inv_rewr _ _ ((y ^ x1) ^ r)).
rewrite -div_pow_distr.
suff -> // : y ^ x1 ^ r * y ^ x2 / z2 / y ^ x1 ^ r = y ^ x2 / z2.
rewrite (mulcC (y ^ x1 ^ r)) -mulcA (mulcC (inv z2)) mulcA; congr.
by rewrite -mulcA mulcV mulc1.
qed.

lemma div_eq_I (x y : group) : i = x / y  <=> x = y.
proof.
have := gen_def x => [[xe]] ->.
have := gen_def y => [[ye]] ->.
have g_neq_i : g <> i.
- rewrite /i -exp1 -expM ZPF.mulr0 log_bij !loggK.
  by rewrite ZPF.oner_neq0.
rewrite -expB !exp_rewr // -ZPF.subr_eq.
rewrite ZPF.add0r; smt(ZPF.opprK).
qed.

const qO : int. (* bound on calls *)
axiom qO_pos : 0 < qO.

module type O = {
  proc check (z1 z2 y : group) : bool
}.

(* What kind of restriction was present? *)
(* Is https://github.com/EasyCrypt/easycrypt/blob/2271abebfa23ea7c5789f378546fce4750452c83/doc/theories.tex
   relevant? *)
module type Adv (O : O) = {
  proc run (x1 : group, x2 : group) : bool (* {* O.check} *)
}.

module M = {
 var r, s         : exp
 var gx1, gx2     : group
 var bad          : bool
 var cO           : int
 var bad_query    : int option
 var bad_guess    : int
 var gz1, gz2, gy : group
}.

(* Copy axiomes from Cyclic_group_prime.ec *)
require import Distr.
search mu.
op dgrp: group distr.

axiom supp_def (s : group) : s \in dgrp.

axiom mu1_def_in (s : group) : mu1 dgrp s = 1%r / G.order%r.

axiom lossless: weight dgrp = 1%r.

module Trapdoor1 (A : Adv) ={
  module TD : O = {
    proc check (z1 z2 y : group) : bool ={
      var r : bool <- false;

      if (M.cO < qO) {
        r    <- (z1 = y ^(loge M.gx1) /\ z2 = y ^ (loge M.gx2));
        M.cO <- M.cO + 1;
      }
      return r;
    }
  }

  module AT = A(TD)
  proc main () : bool = {
    var b : bool;

    M.gx1       <$ dgrp;
    M.r         <$ FD.dt;
    M.s         <$ FD.dt;
    M.gx2       <- (g ^ M.s) / (M.gx1 ^ M.r);
    M.cO        <- 0;
    M.bad_query <- None;
    b           <@ AT.run(M.gx1, M.gx2);
    return b;
  }
}.

module Trapdoor2( A : Adv) ={
  module TD : O = {
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO){
        r    <- ((z1 ^ M.r) * z2 = y ^ M.s);
        M.cO <- M.cO + 1;
      }
      return r ;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
  var b : bool;

  M.gx1       <$ dgrp;
  M.r         <$ dt;
  M.s         <$ dt;
  M.gx2       <- (g ^ M.s) / (M.gx1 ^ M.r);
  M.cO        <- 0;
  M.bad_query <- None;
  b           <@ AT.run(M.gx1, M.gx2);
  return b;
  }
}.

section.

declare module A <: Adv {-M}.

axiom run_ll : forall (O <: O{-A}), islossless O.check => islossless A(O).run.

module G1 (A : Adv) ={
  module TD : O = {
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO) {
        r    <- (z1 / (y ^ (loge M.gx1))) ^ M.r = (y ^ (loge M.gx2)) / z2;
        M.cO <- M.cO + 1;
        if (z1 <> (y ^ (loge M.gx1)) /\
            ((z1 / (y ^ (loge M.gx1))) ^ M.r = (y ^ (loge M.gx2)) / z2)) {
          M.bad <- true;
        }
      }
    return r;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
    var b : bool;

    M.gx1       <$ dgrp;
    M.r         <$ dt;
    M.s         <$ dt;
    M.gx2       <- (g ^ M.s) / (M.gx1 ^ M.r);
    M.bad       <- false;
    M.cO        <- 0;
    M.bad_query <- None;
    b           <@ AT.run(M.gx1, M.gx2);
    return b;
  }
}.

local equiv Eq1 :
Trapdoor2(A).main ~ G1(A).main : ={glob A} ==> ={res}.
proof.
 proc.
 call (_ : ={M.gx1, M.gx2, M.r, M.s, M.cO} /\ (M.gx2 = g ^ M.s / M.gx1 ^ M.r){2}).
 proc; wp; skip; progress.
 have -> := test_rewrite y{2} z1{2} z2{2} M.r{2} M.s{2} (loge M.gx1{2}) (loge (g ^ M.s{2} / M.gx1{2} ^ M.r{2})) _ => //.
 rewrite log_div_minus.
 rewrite loggK.
 rewrite logrzM.
 rewrite ZPF.addrCA ZPF.subrr.
 by rewrite ZPF.addr0.
 by wp; do 3! rnd; skip; progress => //.
qed.

local lemma Pr1 &m :
Pr [Trapdoor2(A).main() @ &m : res] =
Pr [G1(A).main() @ &m : res].
proof.
by byequiv => //; conseq Eq1 => //.
qed.

local equiv Eq2 :
  Trapdoor1(A).main ~ G1(A).main : ={glob A} ==> ! M.bad{2} => ={res}.
proof.
 proc.
 call (_ : M.bad,
          ={M.gx1, M.gx2, M.r, M.s, M.cO} /\ (M.gx2 = g ^ M.s / M.gx1 ^ M.r){2}) => //.
 apply run_ll.
 proc; wp; skip; progress => //.
 have: (z1{2} = y{2} ^ loge M.gx1{2} /\ z2{2} = y{2} ^ loge (g ^ M.s{2} / M.gx1{2} ^ M.r{2}) <=>
((z1{2} / y{2} ^ loge M.gx1{2}) ^ M.r{2} = y{2} ^ loge (g ^ M.s{2} / M.gx1{2} ^ M.r{2}) / z2{2})); last by smt.
 split.
 move=> [heq1 heq2].
 by rewrite heq1 heq2 !mulcV -(exp0 g) -expM ZPF.mul0r.
 move=> heq.
 have :( z1{2} = y{2} ^ loge M.gx1{2} \/
       ! (z1{2} / y{2} ^ loge M.gx1{2}) ^ M.r{2} = y{2} ^ loge (g ^ M.s{2} / M.gx1{2} ^ M.r{2}) / z2{2}) by smt.
 move=> H8.
 elim H8 => heq'.
 split => //.
 have:  (! z2{2} = y{2} ^ loge (g ^ M.s{2} / M.gx1{2} ^ M.r{2}) => false); last by smt.
 move=> hneq; move: heq => /=.
  rewrite heq' mult_div_I I_pow_n.
  rewrite div_eq_I.
 smt.
 smt.
 by move=> ? h; proc; wp.
 by move=> ?; proc; wp; skip.
 by wp; do 3! rnd; skip; progress; smt.
qed.

local lemma Pr2_aux &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [G1(A).main() @ &m : res] + Pr[G1(A).main() @ &m : M.bad].
proof.
 apply (ler_trans (Pr [G1(A).main() @ &m : res \/ M.bad])).
 by byequiv => //; conseq Eq2 => /#.
 by rewrite Pr [mu_or]; smt.
qed.

local lemma Pr2 &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + Pr[G1(A).main() @ &m : M.bad].
proof.
 rewrite (Pr1 &m).
 by apply (Pr2_aux &m).
qed.

module G2 (A : Adv) ={
  module TD : O ={
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO /\ ! M.bad) {
        if (z1 <> (y ^ (loge M.gx1)) /\
            ((z1 / (y ^ (loge M.gx1))) ^ M.r = (y ^ (loge M.gx2)) / z2)) {
          M.bad <- true;
        }
        M.cO <- M.cO + 1;
        r    <- ((z1 / (y ^ (loge M.gx1))) ^ M.r = (y ^ (loge M.gx2)) / z2);
      }
      return r;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
    var b : bool;

    M.gx1       <$ dgrp;
    M.r         <$ dt;
    M.s         <$ dt;
    M.gx2       <$ dgrp;
    M.bad       <- false;
    M.cO        <- 0;
    M.bad_query <- None;
    b           <@ AT.run(M.gx1, M.gx2);
    return b;
  }
}.

local equiv Eq3 :
G1(A).main ~ G2(A).main : ={glob A} ==> M.bad{1} = M.bad{2}.
proof.
 proc.
 wp; call (_ : M.bad,
              ={M.gx1, M.gx2, M.r, M.bad, M.cO},
              ={M.bad}).
 apply run_ll.
 proc; wp; skip; progress; smt.
 by move=> 2?; proc; auto => /> /#.
 by move=> ?; proc; auto => /> /#.
 wp.
 rnd (fun v => g ^ (v - loge M.gx1{2} * M.r{2}))
     (fun u => loge u + M.r{2} * loge M.gx1{2}).
 rnd{2}.
 rnd; rnd; wp; skip; progress => //.
 rewrite ZPF.mulrC -ZPF.addrA.
 by rewrite ZPF.subrr ZPF.addr0 expgK.
 rewrite mu1_def_in dt1E; suff: size G.elems = size G.elems by smt().
 apply uniq_size_uniq; rewrite ?elems_uniq.
 by smt(elemsP G.elemsP).
 by rewrite supp_def.
 rewrite loggK ZPF.addrAC -ZPF.addrA.
 rewrite ZPF.mulrC ZPF.subrr.
 by rewrite ZPF.addr0.
 by rewrite (ZPF.mulrC (loge gx1L)) -logrzM expB expgK.
 by rewrite (ZPF.mulrC (loge gx1L)) -logrzM expB expgK.
 smt.
qed.

local lemma Pr3_aux &m :
Pr[G1(A).main() @ &m : M.bad] =
Pr[G2(A).main() @ &m : M.bad].
proof.
by byequiv => //; conseq Eq3.
qed.

local lemma Pr3 &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + Pr[G2(A).main() @ &m : M.bad].
proof.
 rewrite -(Pr3_aux &m).
 apply (Pr2 &m).
qed.

module G3( A : Adv) = {
  module TD : O = {
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO /\ ! M.bad){
        if (z1 <> (y ^ (loge M.gx1)) /\
            ((z1 / (y ^ (loge M.gx1))) ^ M.r = (y ^ (loge M.gx2)) / z2)) {
          M.bad <- true;
        }
        r    <- (z1 = y ^ (loge M.gx1) /\ z2 = y ^ (loge M.gx2) );
        M.cO <- M.cO + 1;
      }
      return r;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
    var b : bool;

    M.gx1       <$ dgrp;
    M.r         <$ dt;
    M.s         <$ dt;
    M.gx2       <$ dgrp;
    M.bad       <- false;
    M.cO        <- 0;
    M.bad_query <- None;
    b           <@ AT.run(M.gx1, M.gx2);
    return b;
  }
}.

local equiv Eq4 :
G2(A).main ~ G3(A).main : ={glob A} ==> M.bad{1} = M.bad{2}.
proof.
 proc.
 call (_ : M.bad,
         ={M.gx1, M.gx2, M.r, M.bad, M.cO},
         ={M.bad}).
 apply run_ll.
 proc.
 wp; skip; progress.
 have: ((z1{2} / y{2} ^ loge M.gx1{2}) ^ M.r{2} = y{2} ^ loge M.gx2{2} / z2{2}) <=>
(z1{2} = y{2} ^ loge M.gx1{2} /\ z2{2} = y{2} ^ loge M.gx2{2}); last by smt.
 split; last first.
 by move=> [-> ->]; rewrite !mult_div_I I_pow_n.
  move=> H'.
  have :  z1{2} = y{2} ^ loge M.gx1{2} \/
       (z1{2} / y{2} ^ loge M.gx1{2}) ^ M.r{2} <> y{2} ^ loge M.gx2{2} / z2{2}.
 smt.
 move=> {H2} [|] h //.
 move: H'; rewrite h.
 rewrite !mult_div_I I_pow_n.
 progress => //.
 rewrite -I_prod_n H2 div_prod prod_comm group_prod_assoc (prod_comm _ z2{2}).
 by rewrite -div_prod mult_div_I I_prod_n.
 by move=> *; proc; auto => />.
 by move => *; proc; auto => />.
 by wp; do! rnd; skip; progress => //; smt.
qed.

local lemma Pr4_aux &m :
Pr[G2(A).main() @ &m : M.bad] =
Pr[G3(A).main() @ &m : M.bad].
proof.
by byequiv => //; conseq Eq4.
qed.

local lemma Pr4 &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] + Pr[G3(A).main() @ &m : M.bad].
proof.
 rewrite -(Pr4_aux &m).
 apply (Pr3 &m).
qed.

module G4 (A : Adv) = {
  module TD : O = {
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO /\ ! M.bad) {
        if (z1 <> (y ^ (loge M.gx1)) /\
            ((z1 / (y ^ (loge M.gx1))) ^ M.r = (y ^ (loge M.gx2)) / z2)) {
          M.bad       <- true;
          M.bad_query <- Some M.cO;
        }
        r    <- (z1 = y ^ (loge M.gx1) /\ z2 = y ^ (loge M.gx2) );
        M.cO <- M.cO + 1;
      }
      return r;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
    var b : bool;

    M.gx1       <$ dgrp;
    M.r         <$ dt;
    M.s         <$ dt;
    M.gx2       <$ dgrp;
    M.bad       <- false;
    M.cO        <- 0;
    M.bad_query <- None;
    b           <@ AT.run(M.gx1, M.gx2);
    return b;
  }
}.

local equiv Eq5 :
G3(A).main ~ G4(A).main : ={glob A} ==> M.bad{1} <=> M.bad{2} /\ 0 <= oget M.bad_query{2} < qO.
proof.
 proc.
 call (_ : ={M.gx1, M.gx2, M.r, M.bad, M.cO} /\ 0 <= M.cO{2} <= qO /\
             (M.bad{2} => 0 <= oget M.bad_query{2} < M.cO{2} ) /\
             (! M.bad{2} =>  M.bad_query{2} = None ) ).
 proc; wp; skip; progress => //; smt.
 by wp; do! rnd; skip; progress => //; smt.
qed.

local lemma Pr5_aux &m :
Pr[G3(A).main() @ &m : M.bad] =
Pr[G4(A).main() @ &m : M.bad /\ 0 <= oget M.bad_query < qO].
proof.
by byequiv => //; conseq Eq5.
qed.

local lemma Pr5 &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] +
Pr [G4(A).main() @ &m : M.bad /\ 0 <= oget M.bad_query < qO].
proof.
 rewrite -(Pr5_aux &m).
 apply (Pr4 &m).
qed.

module G5 (A : Adv) ={
  module TD : O = {
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO /\ ! M.bad){
        if (z1 <> (y ^ (loge M.gx1)) /\
            ((z1 / (y ^ (loge M.gx1))) ^ M.r = (y ^ (loge M.gx2)) / z2)) {
          M.bad       <- true;
          M.bad_query <- Some M.cO;
        }
        r    <- (z1 = y ^ (loge M.gx1) /\ z2 = y ^ (loge M.gx2) );
        M.cO <- M.cO + 1;
      }
      return r;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
    var b : bool;

    M.gx1       <$ dgrp;
    M.r         <$ dt;
    M.s         <$ dt;
    M.gx2       <$ dgrp;
    M.bad       <- false;
    M.cO        <- 0;
    M.bad_query <- None;
    b           <@ AT.run(M.gx1, M.gx2);
    M.bad_guess <$ [0 .. qO];
    return b;
  }
}.

local equiv Eq6:
G4(A).main ~ G5(A).main : ={glob A} ==> ={M.bad,M.bad_query}.
proof.
 proc.
 seq 8 8: (={M.bad,M.bad_query}); 2: by auto => />; smt.
 seq 7 7: (={glob A, M.gx1, M.r, M.s, M.gx2, M.bad, M.cO, M.bad_query});
   1: by auto => />.
 call (: ={M.gx1, M.r, M.s, M.gx2, M.bad, M.cO, M.bad_query}); 2: by auto.
 by proc; auto => />.
qed.

local lemma Pr6_aux1 &m :
Pr[G4(A).main() @ &m : M.bad /\ 0 <= oget M.bad_query < qO] =
Pr[G5(A).main() @ &m : M.bad /\ 0 <= oget M.bad_query < qO].
proof.
by byequiv => //; conseq Eq6.
qed.

local lemma Pr6_aux2 &m :
Pr[G5(A).main() @ &m : M.bad /\ 0 <= oget M.bad_query < qO] <=
qO%r * Pr[G5(A).main() @ &m : M.bad /\ oget M.bad_query = M.bad_guess].
proof.
 admit. (* don't know how to prove this here. used to be "by compute" *)
qed.

local lemma Pr6 &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] +
qO%r *Pr[G5(A).main() @ &m : M.bad /\ oget M.bad_query = M.bad_guess].
proof.
 apply (ler_trans
     (Pr[Trapdoor2(A).main() @ &m : res] +
      Pr[G5(A).main() @ &m : M.bad /\ 0 <= oget M.bad_query < qO]) _).
 rewrite -(Pr6_aux1 &m).
 apply (Pr5 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply (Pr6_aux2 &m).
qed.

module G6 (A : Adv) = {
  module TD : O = {
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO /\ ! M.bad){
        if (M.cO = M.bad_guess) {
          M.gz1 <- z1;
          M.gz2 <- z2;
          M.gy  <- y;
          if (M.gz1 <> (M.gy ^ (loge M.gx1)) /\
              ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r =
               (M.gy ^ (loge M.gx2)) / M.gz2) ) {
            M.bad       <- true;
            M.bad_query <- Some M.cO;
          }
        }
        r    <- (z1 = y ^ (loge M.gx1) /\ z2 = y ^ (loge M.gx2) );
        M.cO <- M.cO + 1;
      }
      return r;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
    var b : bool;

    M.gz1       <- i;
    M.gz2       <- i;
    M.gy        <- i;
    M.gx1       <$ dgrp;
    M.r         <$ dt;
    M.s         <$ dt;
    M.gx2       <$ dgrp;
    M.bad       <- false;
    M.cO        <- 0;
    M.bad_query <- None;
    M.bad_guess <$ [0 .. qO];
    b           <@ AT.run(M.gx1, M.gx2);
    return b;
  }
}.

local equiv Eq7:
G5(A).main ~ G6(A).main : ={glob A} ==> (M.bad /\ oget M.bad_query = M.bad_guess){1} =>
                                        (M.bad /\ oget M.bad_query = M.bad_guess /\
 (M.gz1 <> (M.gy ^ (loge M.gx1)) /\
         ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2))){2}.
proof.
symmetry.
proc.
swap{2} 9 -1.
call (_ : M.bad /\ M.bad_query <> None /\ oget M.bad_query <> M.bad_guess,
          ={M.gx1, M.r, M.gx2, M.s, M.bad, M.bad_guess, M.bad_query, M.cO} /\
        ( M.bad{1} => (M.gz1 <> (M.gy ^ (loge M.gx1)) /\
         ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2)){1}) /\
       (M.bad_query{2} = None => M.bad_query{1} = None) /\
       ((M.bad_query{2} <> None /\ oget M.bad_query{2} = M.bad_guess{2}) => M.bad{1})).
apply run_ll.
proc.
seq 1 1 :
( ! (M.bad{2} /\ r{2} = false /\
     ! M.bad_query{2} = None /\ ! oget M.bad_query{2} = M.bad_guess{2}) /\
  ={z1, z2, y, r} /\
  ={M.gx1, M.r, M.gx2, M.s, M.bad, M.bad_guess, M.bad_query, M.cO} /\
( M.bad{1} => (M.gz1 <> (M.gy ^ (loge M.gx1)) /\
         ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2)){1}) /\
   (M.bad_query{2} = None => M.bad_query{1} = None) /\
  ((M.bad_query{2} <> None /\ oget M.bad_query{2} = M.bad_guess{2}) => M.bad{1})).
wp; skip; progress.
if => //.
wp; skip; progress => //; smt.
move=> &2 h; proc; wp; skip; progress.
move=> &2; proc; wp; skip; progress;smt.
by rnd; wp; do! rnd; wp; skip; progress; smt.
qed.

local lemma Pr7_aux &m :
Pr[G5(A).main() @ &m : M.bad /\ oget M.bad_query = M.bad_guess] <=
Pr[G6(A).main() @ &m : M.bad /\ oget M.bad_query = M.bad_guess /\
(M.gz1 <> (M.gy ^ (loge M.gx1)) /\
         ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy^(loge M.gx2)) / M.gz2))].

proof.
by byequiv => //; conseq Eq7.
qed.

local lemma Pr7 &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] +
qO%r *Pr[G6(A).main() @ &m : M.bad /\ oget M.bad_query = M.bad_guess /\
(M.gz1 <> (M.gy ^ (loge M.gx1)) /\
         ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2))].
proof.
apply (ler_trans
(Pr [Trapdoor2(A).main() @ &m : res] +
qO%r *Pr[G5(A).main() @ &m : M.bad /\ oget M.bad_query = M.bad_guess]) _ ).
apply (Pr6 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon; first smt.
 by apply (Pr7_aux &m).
qed.

module G7 (A : Adv) = {
  module TD : O = {
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO) {
        if (M.cO = M.bad_guess) {
          M.gz1 <- z1;
          M.gz2 <- z2;
          M.gy  <- y;
        }
        r    <- (z1 = y ^ (loge M.gx1) /\ z2 = y ^ (loge M.gx2) );
        M.cO <- M.cO + 1;
      }
      return r;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
    var b : bool;

    M.gz1       <- i;
    M.gz2       <- i;
    M.gy        <- i;
    M.gx1       <$ dgrp;
    M.gx2       <$ dgrp;
    M.bad       <- false;
    M.cO        <- 0;
    M.bad_query <- None;
    M.bad_guess <$ [0 .. qO];
    b           <@ AT.run(M.gx1, M.gx2);
    M.r         <$ dt;
    M.s         <$ dt;
    return (M.gz1 <> (M.gy ^ (loge M.gx1)) /\
            ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2));
  }
}.

local equiv Eq8:
G6(A).main ~ G7(A).main : ={glob A} ==>
           (M.bad /\ oget M.bad_query = M.bad_guess /\
           (M.gz1 <> (M.gy ^ (loge M.gx1)) /\
           ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2))){1} =>
           res{2}.
proof.
symmetry.
proc.
swap{1} 11 -6.
swap{1} 12 -6.
call (_ : M.bad,
          ={M.gx1, M.r, M.gx2, M.s, M.cO, M.bad, M.bad_guess} /\
           !M.bad{1} /\
          (M.bad{2} => (M.gz1 <> (M.gy ^ (log M.gx1)) /\
           ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2)){2} /\
            ={M.gy, M.gz1, M.gz2}),
          ={M.gx1, M.r, M.gx2, M.s, M.gy, M.gz1, M.gz2} /\
           (M.gz1 <> (M.gy ^ (loge M.gx1)) /\
           ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2)){2} /\
            M.bad_guess{1} < M.cO{1}).
apply run_ll.
proc.
wp; skip; progress => //; smt.
move=> &2 _; proc; wp; skip; progress => //; smt.
move=> ?; proc; wp; skip; progress => //; smt.
by rnd; wp; do !rnd; wp; skip; progress => //; smt.
qed.

local lemma Pr8_aux &m :
Pr[G6(A).main() @ &m : (M.bad /\ oget M.bad_query = M.bad_guess /\
           (M.gz1 <> (M.gy ^ (loge M.gx1)) /\
           ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2)))] <=
Pr[G7(A).main() @ &m : res].
proof.
by byequiv => //; conseq Eq8.
qed.

local lemma Pr8 &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] +
qO%r *Pr[G7(A).main() @ &m : res].
proof.
apply (ler_trans
(Pr [Trapdoor2(A).main() @ &m : res] +
qO%r * Pr[G6(A).main() @ &m : M.bad /\ oget M.bad_query = M.bad_guess /\
(M.gz1 <> (M.gy ^ (loge M.gx1)) /\
         ((M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2))]) _ ).
apply (Pr7 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon; first smt.
 by apply (Pr8_aux &m).
qed.

module G8 (A : Adv) = {
  module TD : O = {
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO) {
        if (M.cO = M.bad_guess) {
          M.gz1 <- z1;
          M.gz2 <- z2;
          M.gy  <- y;
        }
        r    <- (z1 = y ^ (loge M.gx1) /\ z2 = y ^ (loge M.gx2) );
        M.cO <- M.cO + 1;
      }
      return r;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
    var b : bool;
    var ret : bool;

    M.gz1       <- i;
    M.gz2       <- i;
    M.gy        <- i;
    M.gx1       <$ dgrp;
    M.gx2       <$ dgrp;
    M.bad       <- false;
    M.cO        <- 0;
    M.bad_query <- None;
    M.bad_guess <$ [0 .. qO];
    b           <@ AT.run(M.gx1, M.gx2);
    ret         <- false;
    if (M.gz1 <> (M.gy ^ (loge M.gx1))) {
      M.r <$ dt;
      ret <- (M.gz1 / (M.gy ^ (loge M.gx1))) ^ M.r = (M.gy ^ (loge M.gx2)) / M.gz2;
    }
    return ret;
  }
}.

local equiv Eq9:
G7(A).main ~ G8(A).main : ={glob A} ==> res{1} = res{2}.
proof.
proc.
seq 10 10: (={M.gx1, M.gx2, M.gy, M.gz1, M.gz2}).
seq 9 9: (={glob A, M.gz1, M.gz2, M.gy, M.gx1, M.gx2, M.bad, M.cO,
            M.bad_query, M.bad_guess}); 1: by auto => />.
call (: ={M.gz1, M.gz2, M.gy, M.gx1, M.gx2, M.bad, M.cO,
          M.bad_query, M.bad_guess}); 1: by proc; auto => />.
by auto => />.
sp.
if{2}.
wp.
rnd{1}; rnd.
skip; progress => //; smt.
do! rnd{1}; skip; progress => //; smt.
qed.

local lemma Pr9 &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] +
qO%r *Pr[G8(A).main() @ &m : res].
proof.
 rewrite -(_ : Pr[G7(A).main() @ &m : res] = Pr[G8(A).main() @ &m : res]).
  by byequiv => //; conseq Eq9.
  by apply (Pr8 &m).
qed.

module G9 (A : Adv) = {
  module TD : O = {
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO) {
        if (M.cO = M.bad_guess) {
          M.gz1 <- z1;
          M.gz2 <- z2;
          M.gy  <- y;
        }
        r    <- (z1 = y ^ (loge M.gx1) /\ z2 = y ^ (loge M.gx2) );
        M.cO <- M.cO + 1;
      }
      return r;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
    var b : bool;
    var ret : bool;
    var gw : group;

    M.gz1       <- i;
    M.gz2       <- i;
    M.gy        <- i;
    M.gx1       <$ dgrp;
    M.gx2       <$ dgrp;
    M.bad       <- false;
    M.cO        <- 0;
    M.bad_query <- None;
    M.bad_guess <$ [0 .. qO];
    b           <@ AT.run(M.gx1, M.gx2);
    ret         <- false;
    if (M.gz1 <> (M.gy ^ (loge M.gx1))) {
      gw  <$ dgrp;
      ret <- gw = (M.gy ^ (loge M.gx2)) / M.gz2;
    }
    return ret;
  }
}.

local equiv Eq10:
G8(A).main ~ G9(A).main : ={glob A} ==> res{1} = res{2}.
proof.
 proc.
 seq 11 11: (={M.gx1, M.gx2, M.gy, M.gz1, M.gz2, ret}).
 - seq 10 10: (={M.gx1, M.gx2, M.gy, M.gz1, M.gz2}); 2: by auto.
   seq 9 9: (={glob A, M.gz1, M.gz2, M.gy, M.gx1, M.gx2, M.bad, M.cO,
               M.bad_query, M.bad_guess}); 1: by auto => />.
   call (: ={M.gz1, M.gz2, M.gy, M.gx1, M.gx2, M.bad, M.cO,
             M.bad_query, M.bad_guess}); 1: by proc; auto => />.
   by auto => />.
 if => //.
 wp.
 rnd (fun v : exp => (M.gz1 / M.gy ^ loge M.gx1){2} ^ v)
     (fun v => loge v / ((loge M.gz1 - loge ( M.gy ^ loge M.gx1))){2}).
 skip; progress => //.
 - rewrite -log_div_minus log_bij log_pow_mult.
   rewrite ZPF.mulrAC- ZPF.mulrA.
   rewrite ZPF.mulrV ?ZPF.mulr1 //.
   by rewrite log_div_minus ZPF.subr_eq0 -log_bij.
 - rewrite mu1_def_in dt1E; suff: size G.elems = size G.elems by smt().
   apply uniq_size_uniq; rewrite ?elems_uniq.
   by smt(elemsP G.elemsP).
 - by rewrite supp_def.
 rewrite logrzM log_div_minus -ZPF.mulrA.
 rewrite ZPF.mulrV ?ZPF.mulr1 //.
 by rewrite ZPF.subr_eq0 -log_bij.
qed.

local lemma Pr10 &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] +
qO%r *Pr[G9(A).main() @ &m : res].
proof.
 rewrite -(_ : Pr[G8(A).main() @ &m : res] = Pr[G9(A).main() @ &m : res]).
  by byequiv => //; conseq Eq10.
  by apply (Pr9 &m).
qed.

module G10 (A : Adv) = {
  module TD : O = {
    proc check (z1 z2 y : group) : bool = {
      var r : bool <- false;

      if (M.cO < qO) {
        if (M.cO = M.bad_guess) {
          M.gz1 <- z1;
          M.gz2 <- z2;
          M.gy  <- y;
        }
        r    <- (z1 = y ^ (loge M.gx1) /\ z2 = y ^ (loge M.gx2) );
        M.cO <- M.cO + 1;
      }
      return r;
    }
  }

  module AT = A(TD)

  proc main () : bool = {
    var b : bool;
    var ret : bool;
    var gw : group;

    M.gz1       <- i;
    M.gz2       <- i;
    M.gy        <- i;
    M.gx1       <$ dgrp;
    M.gx2       <$ dgrp;
    M.bad       <- false;
    M.cO        <- 0;
    M.bad_query <- None;
    M.bad_guess <$ [0 .. qO];
    b           <@ AT.run(M.gx1, M.gx2);
    ret         <- false;
    gw          <$ dgrp;
    return ((gw = (M.gy ^ (loge M.gx2)) / M.gz2));
  }
}.

local equiv Eq11:
G9(A).main ~ G10(A).main : ={glob A} ==> res{1} => res{2}.
proof.
proc.
seq 10 10: (={M.gx1, M.gx2, M.gy, M.gz1, M.gz2}).
 - seq 9 9: (={glob A, M.gz1, M.gz2, M.gy, M.gx1, M.gx2, M.bad, M.cO,
               M.bad_query, M.bad_guess}); 1: by auto => />.
   call (: ={M.gz1, M.gz2, M.gy, M.gx1, M.gx2, M.bad, M.cO,
             M.bad_query, M.bad_guess}); 1: by proc; auto => />.
   by auto => />.
sp.
if{1}.
wp.
rnd.
skip; progress => //; smt.
do! rnd{2}; skip; progress => //; smt.
qed.

local lemma Pr11_aux &m :
Pr[G10(A).main() @ &m : res] = 1%r / G.order%r.
proof.
 byphoare => //.
 proc; rnd; wp.
 call (_ : true) => //.
  by apply run_ll.
  by proc; wp.
 rnd; wp; do !rnd; wp; skip; progress; 2: by rewrite lossless.
 rewrite -{2}lossless; apply mu_eq => x; rewrite /predT.
 apply (_ : forall p, p => p = true); first by smt().
 split => [gy gz2|]; rewrite ?mu1_def_in //.
 have -> : 1%r = b2r (0 <= qO) by smt(qO_pos).
 by rewrite -DInterval.weight_dinter; apply mu_eq.
qed.

lemma Conclusion &m :
Pr [Trapdoor1(A).main() @ &m : res] <=
Pr [Trapdoor2(A).main() @ &m : res] +
qO%r * (1%r / G.order%r).
proof.
 rewrite -(Pr11_aux &m).
 apply (ler_trans
       (Pr[Trapdoor2(A).main() @ &m : res] + qO%r * Pr[G9(A).main() @ &m : res]) _).
 apply (Pr10 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon; first smt.
 by byequiv => //; conseq Eq11.
qed.

end section.

print axiom Conclusion.
