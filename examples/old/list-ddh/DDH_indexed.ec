require import Int.
require import Bool.
require import Prime_field.
require import Cyclic_group_prime.
require import Pair.
require import Distr.

(* We define the following modules:
   - Sample_DH: provide functions that sample real
       and random DH triples
   - DDH_real: The real DDH experiment
   - DDH_random: The random DDH experiment

   - Sample_DH_distr: Provide functions that sample real
       and random DH triples defined in terms
       of distributions using Dprod and Dapply.
   - DDH_distr_real and DDH_distr_random: Same experiments
       as above, only defined in term Sample_DH_distr.

   We prove the following lemmas:
   - Eq_Sample_DH_distr_real: The functions for
     sampling real DH triples in Sample_DH and Sample_DH_distr
     are equivalent.
   - Eq_Sample_DH_distr_random: The functions for
       sampling random DH triples in Sample_DH and Sample_DH_distr
       are equivalent.
   - Eq_DDH_real_distr, Eq_DDH_random_distr: The two versions of
       the DDH games coincide.
*)

type gtriple =  (group * group * group).

module type DDH_DISTINGUISHER = { 
  fun distinguish(i : int, X Y Z : group) : bool
}.

module Sample_DH = {
  fun sample_dh_real() : gtriple = {
    var x, y : gf_q;
    x  = $Dgf_q.dgf_q;
    y  = $Dgf_q.dgf_q;
    return (g^x, g^y, g^(x*y));
  }

  fun sample_dh_random() : gtriple = {
    var x, y, z : gf_q;
    x  = $Dgf_q.dgf_q;
    y  = $Dgf_q.dgf_q;
    z  = $Dgf_q.dgf_q;
    return (g^x, g^y, g^z);
  }
}.

module DDH_real (D:DDH_DISTINGUISHER) = { 
  fun main(i : int) : bool = {
    var x, y, z : group;
    var b : bool;
    (x,y,z) = Sample_DH.sample_dh_real();
    b = D.distinguish(i,x,y,z);
    return b;
  }     
}.

module DDH_random (D:DDH_DISTINGUISHER) = { 
  fun main(i:int) : bool = {
    var x, y, z : group;
    var b : bool;
    (x,y,z) = Sample_DH.sample_dh_random();
    b = D.distinguish(i,x,y,z);
    return b;
  }
}.

(*************************************************************************)
(* We also provide an equivalent version where the distributions
   of the triples are directly defined. *)

op d_dh_triple : gtriple distr =
  Dapply.dapply (lambda z, let (a,b) = z in (g^a, g^b, g^(a*b)))
    (Dprod.dprod Dgf_q.dgf_q Dgf_q.dgf_q).

op d_random_triple : gtriple distr =
  Dapply.dapply (lambda z, let (ab,c) = z in let (a,b) = ab in (g^a, g^b, g^c))
    (Dprod.dprod (Dprod.dprod Dgf_q.dgf_q Dgf_q.dgf_q) Dgf_q.dgf_q).

module Sample_DH_distr = {
  fun sample_dh_real() : gtriple = {
    var g1, g2, g3 : group;
    (g1, g2, g3)  = $d_dh_triple;
    return (g1, g2, g3);
  }

  fun sample_dh_random() : gtriple = {
    var g1, g2, g3 : group;
    (g1, g2, g3)  = $d_random_triple;
    return (g1, g2, g3);
  }
}.

module DDH_distr_real (D:DDH_DISTINGUISHER) = { 
  fun main(i : int) : bool = {
    var x, y, z : group;
    var b : bool;
    (x,y,z) = Sample_DH_distr.sample_dh_real();
    b = D.distinguish(i,x,y,z);
    return b;
  }     
}.

module DDH_distr_random (D:DDH_DISTINGUISHER) = { 
  fun main(i : int) : bool = {
    var x, y, z : group;
    var b : bool;
    (x,y,z) = Sample_DH_distr.sample_dh_random();
    b = D.distinguish(i,x,y,z);
    return b;
  }
}.

require import Real.

theory Equiv_Dprod.
  type a.
  type b.
  
  const da : a distr.
  const db : b distr.

  module Sample_dprod = {
    fun sample() : (a * b) = {
      var r : (a * b);
      r = $Dprod.dprod da db;
      return r;
    }
  }.

  module Sample_twice = {
    fun sample() : (a * b) = {
      var ra : a;
      var rb : b;
      ra = $da;
      rb = $db;
      return (ra, rb);
    }
  }.

  lemma eq_twice_dprod:
      equiv[  Sample_twice.sample ~ Sample_dprod.sample :
             true ==> ={res} ].
  proof strict.
    bypr (res{1}) (res{2}).
      progress.
    move=> rab &m1 &m2 _.
    pose ra' := fst rab. 
    pose rb' := snd rab.
    cut -> :(  Pr[Sample_dprod.sample() @ &m2 : rab = res]
             = mu_x da ra' * mu_x db rb').
    bdhoare_deno (_ : true ==> (ra', rb')=res).
      fun.
      rnd.
      skip.
      progress.
      cut ->: (  mu   (Dprod.dprod da db) (lambda (x : (a * b)), (ra', rb') = x)
               = mu_x (Dprod.dprod da db) (ra', rb')).
      rewrite /mu_x. congr. apply fun_ext => //.
    rewrite Dprod.mu_x_def => //.
    by trivial.
    by smt.
    bdhoare_deno (_ : true ==> (ra', rb')=res).
      fun.
    rnd (ra' = ra)
        (mu_x da ra')
        (mu_x db rb')
        (weight da - mu_x da ra')
        (0%r)
        (lambda rb, rb' = rb /\ ra = ra'). smt.
    rnd.
    skip. progress.
      rewrite /mu_x.
      cut -> : ((lambda (x : a), ra' = x) = ((=) ra')).
        apply fun_ext. by trivial.
      trivial.
    progress.
   rewrite /mu_x.
   cut -> : ((lambda (x : b), rb' = x) = ((=) rb')).
     apply fun_ext. by trivial.
   trivial.
   rnd. skip. progress.
   cut -> :  ((lambda (x : a), ! ra' = x) = 
             (cpNot (lambda (x : a), ra' = x))).
     apply fun_ext.
     smt.
     rewrite mu_not /weight /mu_x.
     cut -> : (lambda (x : a), ra' = x) = ((=) ra').
       apply fun_ext. smt.
    smt.
    progress.
    cut -> : ((lambda (rb : b), rb' = rb /\ ra{hr} = ra') = cpFalse).
      apply fun_ext. smt. smt.
    by trivial.
    by smt.
  qed.

end Equiv_Dprod.

theory Equiv_Dapply.
  type a.
  type b.
  
  const da : a distr.

  op f : a -> b.

  module Sample_dapply = {
    fun sample() : b = {
      var r : b;
      r = $Dapply.dapply f da;
      return r;
    }
  }.

  module Sample_then_apply = {
    fun sample() : b = {
      var ra : a;
      ra = $da;
      return (f ra);
    }
  }.

  lemma eq_apply_dapply:
      equiv[ Sample_then_apply.sample ~ Sample_dapply.sample :
             true ==> ={res} ].
  proof strict.
    bypr (res{1}) (res{2}).
      progress.
    move=> rb &m1 &m2 _.
    cut -> :(  Pr[Sample_dapply.sample() @ &m2 : rb= res]
               = mu da (lambda r, f r = rb)).
    bdhoare_deno (_ : true ==> (rb=res)).
      fun.
      rnd.
      skip.
      progress.
      rewrite Dapply.mu_def.
      cut ->: ((lambda (x : a), (lambda (x0 : b), rb = x0) (f x)) =
               (lambda (r : a), f r = rb)).
      apply fun_ext. by smt.
      by trivial.
      by trivial.
      by trivial.
    bdhoare_deno (_ : true ==> (rb=res)).
      fun.
      rnd.
      skip.
      progress.
      cut -> : (lambda (x : a), rb = f x) = (lambda (r : a), f r = rb).
        apply fun_ext. smt.
      smt.
      by trivial.
      by trivial.
  qed.

end Equiv_Dapply.

(** We now perform the equivalence proofs between Sample_DH and Sample_DH_distr
    using the lemmas proved about dprod and dapply *)

(*************************************************************************)
(* First for sample_dh_random *)
clone Equiv_Dprod as E1_ra
  with type a = gf_q, type b = gf_q, op da = Dgf_q.dgf_q, op db = Dgf_q.dgf_q.

module type S1_ra = { fun sample() : gf_q * gf_q }.
module T1(S : S1_ra) = {
  fun sample_dh_random() : gtriple = {
    var x, y, z : gf_q;
    (x,y)  = S.sample();
    z  = $Dgf_q.dgf_q;
    return (g^x, g^y, g^z);
  }
}.
module T1_left  = T1(E1_ra.Sample_twice).
module T1_right = T1(E1_ra.Sample_dprod).

clone Equiv_Dprod as E2_ra
  with type a = (gf_q * gf_q), type b = gf_q,
       op da = Dprod.dprod Dgf_q.dgf_q Dgf_q.dgf_q, op db = Dgf_q.dgf_q.

module type S2_ra = { fun sample() : (gf_q * gf_q) * gf_q }.
module T2(S : S2_ra) = {
  fun sample_dh_random() : gtriple = {
    var x, y, z : gf_q;
    var xy : gf_q * gf_q;
    (xy,z) = S.sample();
    (x,y) = xy;
    return (g^x, g^y, g^z);
  }
}.
module T2_left  = T2(E2_ra.Sample_twice).
module T2_right = T2(E2_ra.Sample_dprod).

clone Equiv_Dapply as E3_ra
  with type a = ((gf_q * gf_q) * gf_q), type b = gtriple,
       op da = Dprod.dprod (Dprod.dprod Dgf_q.dgf_q Dgf_q.dgf_q) Dgf_q.dgf_q,
       op f = (lambda x , let (ab,c) = x in let (a,b) = ab in (g^a, g^b, g^c)).

module type S3_ra = { fun sample() : gtriple }.
module T3(S : S3_ra) = {
  fun sample_dh_random() : gtriple = {
    var r : gtriple;
    r = S.sample();
    return r;
  }
}.
module T3_left  = T3(E3_ra.Sample_then_apply).
module T3_right = T3(E3_ra.Sample_dapply).

lemma Eq_Sample_DH_T1_left: 
  equiv[ Sample_DH.sample_dh_random ~ T1_left.sample_dh_random : true ==> ={res} ].
proof strict.
  fun. inline E1_ra.Sample_twice.sample. rnd. wp. do rnd. skip; progress; smt.
qed.

lemma Eq_T1_left_T1_right: 
  equiv[ T1_left.sample_dh_random ~ T1_right.sample_dh_random : true ==> ={res} ].
proof strict.
  fun. seq 1 1: (={x,y}). call E1_ra.eq_twice_dprod; skip. smt. rnd; skip. smt.
qed.

lemma Eq_T1_right_T2_left:
  equiv[ T1_right.sample_dh_random ~ T2_left.sample_dh_random : true ==> ={res} ].
proof strict.
  fun. inline  E1_ra.Sample_dprod.sample.
  inline E2_ra.Sample_twice.sample. wp. rnd. wp. rnd. skip. smt.
qed.

lemma Eq_T2_left_T2_right:
  equiv[ T2_left.sample_dh_random ~ T2_right.sample_dh_random : true ==> ={res} ].
proof strict.
  fun. wp. call E2_ra.eq_twice_dprod; skip. smt.
qed.

lemma Eq_T2_right_T3_left:
  equiv[ T2_right.sample_dh_random ~ T3_left.sample_dh_random : true ==> ={res} ].
proof strict.
  fun. inline  E2_ra.Sample_dprod.sample. inline E3_ra.Sample_then_apply.sample.
  wp. rnd. skip. smt.
qed.

lemma Eq_T3_left_T3_right:
  equiv[ T3_left.sample_dh_random ~ T3_right.sample_dh_random : true ==> ={res} ].
proof strict.
  fun. call E3_ra.eq_apply_dapply. skip; smt.
qed.

lemma Eq_T3_right_Sample_DH_distr:
  equiv[  T3_right.sample_dh_random ~ Sample_DH_distr.sample_dh_random : true ==> ={res} ].
proof strict.
  fun. inline E3_ra.Sample_dapply.sample.
  wp. rnd. skip. progress. smt.
qed.

lemma Eq_Sample_DH_distr_random:
  equiv[ Sample_DH.sample_dh_random ~ Sample_DH_distr.sample_dh_random : true ==> ={res} ].
proof strict.
  bypr (res{1}) (res{2}). by smt.
  move=> a &m1 &m2 _.
  cut -> :   Pr[Sample_DH.sample_dh_random() @ &m1 : a = res]
           = Pr[T1_left.sample_dh_random() @ &m1 : a = res].
  by equiv_deno Eq_Sample_DH_T1_left => // ; smt.
  cut -> :   Pr[T1_left.sample_dh_random() @ &m1 : a = res]
           = Pr[T1_right.sample_dh_random() @ &m1 : a = res].
  by equiv_deno Eq_T1_left_T1_right => // ; smt.
  cut -> :   Pr[T1_right.sample_dh_random() @ &m1 : a = res]
           = Pr[T2_left.sample_dh_random() @ &m1 : a = res].
  by equiv_deno Eq_T1_right_T2_left => // ; smt.
  cut -> :   Pr[T2_left.sample_dh_random() @ &m1 : a = res]
           = Pr[T2_right.sample_dh_random() @ &m1 : a = res].
  by equiv_deno Eq_T2_left_T2_right => // ; smt.
  cut -> :   Pr[T2_right.sample_dh_random() @ &m1 : a = res]
           = Pr[T3_left.sample_dh_random() @ &m1 : a = res].
  by equiv_deno Eq_T2_right_T3_left => // ; smt.
  cut -> :   Pr[T3_left.sample_dh_random() @ &m1 : a = res]
           = Pr[T3_right.sample_dh_random() @ &m2 : a = res].
  by equiv_deno Eq_T3_left_T3_right => // ; smt.
  by equiv_deno Eq_T3_right_Sample_DH_distr => // ; smt.
qed.

(*************************************************************************)
(* Then for sample_dh_real *)
clone Equiv_Dprod as E1_re
  with type a = gf_q, type b = gf_q, op da = Dgf_q.dgf_q, op db = Dgf_q.dgf_q.

module type S1_re = { fun sample() : gf_q * gf_q }.
module S1(S : S1_re) = {
  fun sample_dh_real() : gtriple = {
    var x, y : gf_q;
    (x,y) = S.sample();
    return (g^x, g^y, g^(x*y));
  }
}.
module S1_left  = S1(E1_re.Sample_twice).
module S1_right = S1(E1_re.Sample_dprod).

clone Equiv_Dapply as E2_re
  with type a = (gf_q * gf_q), type b = gtriple,
       op da = (Dprod.dprod Dgf_q.dgf_q Dgf_q.dgf_q),
       op f = (lambda x , let (a,b) = x in (g^a, g^b, g^(a*b))).

module type S2_re = { fun sample() : gtriple }.
module S2(S : S2_re) = {
  fun sample_dh_real() : gtriple = {
    var r : gtriple;
    r = S.sample();
    return r;
  }
}.
module S2_left  = S2(E2_re.Sample_then_apply).
module S2_right = S2(E2_re.Sample_dapply).

lemma Eq_Sample_DH_S1_left: 
  equiv[ Sample_DH.sample_dh_real ~ S1_left.sample_dh_real : true ==> ={res} ].
proof strict.
  fun. inline E1_re.Sample_twice.sample. wp. rnd. rnd. skip; progress; smt.
qed.

lemma Eq_S1_left_S1_right: 
  equiv[ S1_left.sample_dh_real ~ S1_right.sample_dh_real : true ==> ={res} ].
proof strict.
  fun. seq 1 1: (={x,y}). call E1_re.eq_twice_dprod; skip. smt. skip. smt.
qed.

lemma Eq_S1_right_S2_left:
  equiv[ S1_right.sample_dh_real ~ S2_left.sample_dh_real : true ==> ={res} ].
proof strict.
  fun. inline  E1_re.Sample_dprod.sample. inline E2_re.Sample_then_apply.sample.
  wp. rnd. skip. smt.
qed.

lemma Eq_S2_left_S2_right:
  equiv[ S2_left.sample_dh_real ~ S2_right.sample_dh_real : true ==> ={res} ].
proof strict.
  fun. wp. call E2_re.eq_apply_dapply; skip. smt.
qed.

lemma Eq_S2_right_Sample_DH_distr:
  equiv[  S2_right.sample_dh_real ~ Sample_DH_distr.sample_dh_real : true ==> ={res} ].
proof strict.
  fun. inline E2_re.Sample_dapply.sample.
  wp. rnd. skip. progress. smt.
qed.

lemma Eq_Sample_DH_distr_real:
  equiv[ Sample_DH.sample_dh_real ~ Sample_DH_distr.sample_dh_real : true ==> ={res} ].
proof strict.
  bypr (res{1}) (res{2}). by smt.
  move=> a &m1 &m2 _.
  cut -> :   Pr[Sample_DH.sample_dh_real() @ &m1 : a = res]
           = Pr[S1_left.sample_dh_real() @ &m1 : a = res].
  by equiv_deno Eq_Sample_DH_S1_left => // ; smt.
  cut -> :   Pr[S1_left.sample_dh_real() @ &m1 : a = res]
           = Pr[S1_right.sample_dh_real() @ &m1 : a = res].
  by equiv_deno Eq_S1_left_S1_right => // ; smt.
  cut -> :   Pr[S1_right.sample_dh_real() @ &m1 : a = res]
           = Pr[S2_left.sample_dh_real() @ &m1 : a = res].
  by equiv_deno Eq_S1_right_S2_left => // ; smt.
  cut -> :   Pr[S2_left.sample_dh_real() @ &m1 : a = res]
           = Pr[S2_right.sample_dh_real() @ &m1 : a = res].
  by equiv_deno Eq_S2_left_S2_right => // ; smt.
  by equiv_deno Eq_S2_right_Sample_DH_distr => // ; smt.
qed.

lemma Eq_DDH_real_distr:
  forall (D <: DDH_DISTINGUISHER {DDH_real, DDH_distr_real}),
    equiv[ DDH_real(D).main ~ DDH_distr_real(D).main :
           ={glob D,i} ==> ={res} ].
proof strict.
  move=> D.
  fun. call (_ : true). call Eq_Sample_DH_distr_real. skip; smt.
qed.

lemma Eq_DDH_random_distr:
  forall (D <: DDH_DISTINGUISHER {DDH_real, DDH_distr_real}),
    equiv[ DDH_random(D).main ~ DDH_distr_random(D).main :
           ={glob D, i} ==> ={res} ].
proof strict.
  move=> D.
  fun. call (_ : true). call Eq_Sample_DH_distr_random. skip; smt.
qed.