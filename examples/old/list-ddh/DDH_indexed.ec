require import Int.
require import Bool.
require import Distr.
require import DMap.
require import DProd.

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

require (****) Group.

clone Group.CyclicGroup as G.

axiom prime_p : IntDiv.prime G.order.

clone G.PowZMod as GP with
  lemma prime_order <- prime_p.

clone  GP.FDistr as FD.

import G GP FD GP.ZModE.

type gtriple =  (group * group * group).

module type DDH_DISTINGUISHER = {
  proc distinguish(i : int, x y z : group) : bool
}.

module Sample_DH = {
  proc sample_dh_real() : gtriple = {
    var x, y : exp;

    x <$ FD.dt;
    y <$ FD.dt;
    return (g ^ x, g ^ y, g ^ (x * y));
  }

  proc sample_dh_random() : gtriple = {
    var x, y, z : exp;

    x <$ FD.dt;
    y <$ FD.dt;
    z <$ FD.dt;
    return (g ^ x, g ^ y, g ^ z);
  }
}.

module DDH_real (D : DDH_DISTINGUISHER) = {
  proc main(i : int) : bool = {
    var x, y, z : group;
    var b       : bool;

    (x, y, z) <@ Sample_DH.sample_dh_real();
    b         <@ D.distinguish(i, x, y, z);
    return b;
  }
}.

module DDH_random (D : DDH_DISTINGUISHER) = {
  proc main(i : int) : bool = {
    var x, y, z : group;
    var b       : bool;

    (x, y, z) <@ Sample_DH.sample_dh_random();
    b         <@ D.distinguish(i, x, y, z);
    return b;
  }
}.

(*************************************************************************)
(* We also provide an equivalent version where the distributions
   of the triples are directly defined. *)

op d_dh_triple : gtriple distr =
  dmap (FD.dt `*` FD.dt)
       (fun z : exp * exp =>
          let (a, b) = z in (g ^ a, g ^ b, g ^ (a * b))).

op d_random_triple : gtriple distr =
  dmap ((FD.dt `*` FD.dt) `*` FD.dt)
       (fun z : (exp * exp) * exp =>
          let (ab, c) = z in let (a, b) = ab in (g ^ a, g ^ b, g ^ c)).

module Sample_DH_distr = {
  proc sample_dh_real() : gtriple = {
    var g1, g2, g3 : group;

    (g1, g2, g3) <$d_dh_triple;
    return (g1, g2, g3);
  }

  proc sample_dh_random() : gtriple = {
    var g1, g2, g3 : group;

    (g1, g2, g3) <$d_random_triple;
    return (g1, g2, g3);
  }
}.

module DDH_distr_real (D : DDH_DISTINGUISHER) = {
  proc main(i : int) : bool = {
    var x, y, z : group;
    var b       : bool;

    (x, y, z) <@ Sample_DH_distr.sample_dh_real();
    b         <@ D.distinguish(i,x,y,z);
    return b;
  }
}.

module DDH_distr_random (D : DDH_DISTINGUISHER) = {
  proc main(i : int) : bool = {
    var x, y, z : group;
    var b       : bool;

    (x, y, z) <@ Sample_DH_distr.sample_dh_random();
    b         <@ D.distinguish(i,x,y,z);
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
    proc sample() : a * b = {
      var r : a * b;

      r <$ da `*` db;
      return r;
    }
  }.

  module Sample_twice = {
    proc sample() : a * b = {
      var ra : a;
      var rb : b;

      ra <$ da;
      rb <$ db;
      return (ra, rb);
    }
  }.

  clone import ProdSampling as PS with
    type t1 <- a,
    type t2 <- b
  proof *.

  lemma eq_twice_dprod:
      equiv[  Sample_twice.sample ~ Sample_dprod.sample :
             true ==> ={res} ].
  proof strict.
  transitivity S.sample2 ((da, db) = arg{2} ==> ={res})
                         ((da, db) = arg{1} ==> ={res}); 1, 2: by smt().
  - by proc; auto.
  transitivity S.sample (={arg}             ==> ={res})
                         ((da, db) = arg{1} ==> ={res}); 1, 2: by smt().
  - by symmetry; conseq sample_sample2 => //.
  by proc; auto.
  qed.

end Equiv_Dprod.

theory Equiv_Dapply.
  type a.
  type b.

  const da : a distr.

  op f : a -> b.

  module Sample_dapply = {
    proc sample() : b = {
      var r : b;

      r <$ dmap da f;
      return r;
    }
  }.

  module Sample_then_apply = {
    proc sample() : b = {
      var ra : a;

      ra <$ da;
      return (f ra);
    }
  }.

  clone import DMapSampling as MS with
    type t1 <- a,
    type t2 <- b
  proof *.

  lemma eq_apply_dapply:
      equiv[ Sample_then_apply.sample ~ Sample_dapply.sample :
             true ==> ={res} ].
  proof strict.
  transitivity S.map ((da, f) = arg{2} ==> ={res})
                     ((da, f) = arg{1} ==> ={res}); 1, 2: by smt().
  - by proc; auto.
  transitivity S.sample (={arg}           ==> ={res})
                        ((da, f) = arg{1} ==> ={res}); 1, 2: by smt().
  - by symmetry; conseq sample => //.
  by proc; auto.
  qed.

end Equiv_Dapply.

(** We now perform the equivalence proofs between Sample_DH and Sample_DH_distr
    using the lemmas proved about dprod and dapply *)

(*************************************************************************)
(* First for sample_dh_random *)
clone Equiv_Dprod as E1_ra
  with type a = exp, type b = exp, op da = FD.dt, op db = FD.dt.

module type S1_ra = { proc sample() : exp * exp }.
module T1 (S : S1_ra) = {
  proc sample_dh_random() : gtriple = {
    var x, y, z : exp;

    (x, y) <@ S.sample();
    z      <$ FD.dt;
    return (g ^ x, g ^ y, g ^ z);
  }
}.

module T1_left  = T1(E1_ra.Sample_twice).
module T1_right = T1(E1_ra.Sample_dprod).

clone Equiv_Dprod as E2_ra
  with type a = (exp * exp), type b = exp,
       op da = FD.dt `*` FD.dt, op db = FD.dt.

module type S2_ra = { proc sample() : (exp * exp) * exp }.

module T2 (S : S2_ra) = {
  proc sample_dh_random() : gtriple = {
    var x, y, z : exp;
    var xy      : exp * exp;

    (xy, z) <@ S.sample();
    (x,y)   <- xy;
    return (g ^ x, g ^ y, g ^ z);
  }
}.

module T2_left  = T2(E2_ra.Sample_twice).
module T2_right = T2(E2_ra.Sample_dprod).

clone Equiv_Dapply as E3_ra
  with type a = ((exp * exp) * exp), type b = gtriple,
       op da = (FD.dt `*` FD.dt) `*` FD.dt,
       op f = (fun z : (exp * exp) * exp =>
                 let (ab, c) = z in let (a, b) = ab in (g ^ a, g ^ b, g ^ c)).

module type S3_ra = { proc sample() : gtriple }.

module T3 (S : S3_ra) = {
  proc sample_dh_random() : gtriple = {
    var r : gtriple;

    r <@ S.sample();
    return r;
  }
}.

module T3_left  = T3(E3_ra.Sample_then_apply).
module T3_right = T3(E3_ra.Sample_dapply).

lemma Eq_Sample_DH_T1_left:
  equiv[ Sample_DH.sample_dh_random ~ T1_left.sample_dh_random : true ==> ={res} ].
proof strict.
  proc. inline E1_ra.Sample_twice.sample. rnd. wp. do rnd. skip; progress; smt.
qed.

lemma Eq_T1_left_T1_right:
  equiv[ T1_left.sample_dh_random ~ T1_right.sample_dh_random : true ==> ={res} ].
proof strict.
  proc. seq 1 1: (={x,y}). call E1_ra.eq_twice_dprod; skip. smt. rnd; skip. smt.
qed.

lemma Eq_T1_right_T2_left:
  equiv[ T1_right.sample_dh_random ~ T2_left.sample_dh_random : true ==> ={res} ].
proof strict.
  proc. inline  E1_ra.Sample_dprod.sample.
  inline E2_ra.Sample_twice.sample. wp. rnd. wp. rnd. skip. smt.
qed.

lemma Eq_T2_left_T2_right:
  equiv[ T2_left.sample_dh_random ~ T2_right.sample_dh_random : true ==> ={res} ].
proof strict.
  proc. wp. call E2_ra.eq_twice_dprod; skip. smt.
qed.

lemma Eq_T2_right_T3_left:
  equiv[ T2_right.sample_dh_random ~ T3_left.sample_dh_random : true ==> ={res} ].
proof strict.
  proc. inline  E2_ra.Sample_dprod.sample. inline E3_ra.Sample_then_apply.sample.
  wp. rnd. skip. smt.
qed.

lemma Eq_T3_left_T3_right:
  equiv[ T3_left.sample_dh_random ~ T3_right.sample_dh_random : true ==> ={res} ].
proof strict.
  proc. call E3_ra.eq_apply_dapply. skip; smt.
qed.

lemma Eq_T3_right_Sample_DH_distr:
  equiv[  T3_right.sample_dh_random ~ Sample_DH_distr.sample_dh_random : true ==> ={res} ].
proof strict.
  proc. inline E3_ra.Sample_dapply.sample.
  wp. auto => /> *. smt.
qed.

lemma Eq_Sample_DH_distr_random:
  equiv[ Sample_DH.sample_dh_random ~ Sample_DH_distr.sample_dh_random : true ==> ={res} ].
proof strict.
transitivity T1_left.sample_dh_random (true ==> ={res}) (true ==> ={res}) => //.
- by conseq Eq_Sample_DH_T1_left.
transitivity T1_right.sample_dh_random (true ==> ={res}) (true ==> ={res}) => //.
- by conseq Eq_T1_left_T1_right.
transitivity T2_left.sample_dh_random (true ==> ={res}) (true ==> ={res}) => //.
- by conseq Eq_T1_right_T2_left.
transitivity T2_right.sample_dh_random (true ==> ={res}) (true ==> ={res}) => //.
- by conseq Eq_T2_left_T2_right.
transitivity T3_left.sample_dh_random (true ==> ={res}) (true ==> ={res}) => //.
- by conseq Eq_T2_right_T3_left.
transitivity T3_right.sample_dh_random (true ==> ={res}) (true ==> ={res}) => //.
- by conseq Eq_T3_left_T3_right.
by conseq Eq_T3_right_Sample_DH_distr.
qed.

(*************************************************************************)
(* Then for sample_dh_real *)
clone Equiv_Dprod as E1_re
  with type a = exp, type b = exp, op da = FD.dt, op db = FD.dt.

module type S1_re = { proc sample() : exp * exp }.

module S1 (S : S1_re) = {
  proc sample_dh_real() : gtriple = {
    var x, y : exp;

    (x, y) <@ S.sample();
    return (g ^ x, g ^ y, g ^ (x * y));
  }
}.

module S1_left  = S1(E1_re.Sample_twice).
module S1_right = S1(E1_re.Sample_dprod).

clone Equiv_Dapply as E2_re
  with type a = (exp * exp), type b = gtriple,
       op da = FD.dt `*` FD.dt,
       op f = (fun z : exp * exp =>
                 let (a, b) = z in (g ^ a, g ^ b, g ^ (a * b))).

module type S2_re = { proc sample() : gtriple }.

module S2 (S : S2_re) = {
  proc sample_dh_real() : gtriple = {
    var r : gtriple;

    r <@ S.sample();
    return r;
  }
}.

module S2_left  = S2(E2_re.Sample_then_apply).
module S2_right = S2(E2_re.Sample_dapply).

lemma Eq_Sample_DH_S1_left:
  equiv[ Sample_DH.sample_dh_real ~ S1_left.sample_dh_real : true ==> ={res} ].
proof strict.
  proc. inline E1_re.Sample_twice.sample. wp. rnd. rnd. skip; progress; smt.
qed.

lemma Eq_S1_left_S1_right:
  equiv[ S1_left.sample_dh_real ~ S1_right.sample_dh_real : true ==> ={res} ].
proof strict.
  proc. seq 1 1: (={x,y}). call E1_re.eq_twice_dprod; skip. smt. skip. smt.
qed.

lemma Eq_S1_right_S2_left:
  equiv[ S1_right.sample_dh_real ~ S2_left.sample_dh_real : true ==> ={res} ].
proof strict.
  proc. inline  E1_re.Sample_dprod.sample. inline E2_re.Sample_then_apply.sample.
  wp. rnd. skip. smt.
qed.

lemma Eq_S2_left_S2_right:
  equiv[ S2_left.sample_dh_real ~ S2_right.sample_dh_real : true ==> ={res} ].
proof strict.
  proc. wp. call E2_re.eq_apply_dapply; skip. smt.
qed.

lemma Eq_S2_right_Sample_DH_distr:
  equiv[  S2_right.sample_dh_real ~ Sample_DH_distr.sample_dh_real : true ==> ={res} ].
proof strict.
  proc. inline E2_re.Sample_dapply.sample.
  wp. auto => /> *. smt.
qed.

lemma Eq_Sample_DH_distr_real:
  equiv[ Sample_DH.sample_dh_real ~ Sample_DH_distr.sample_dh_real : true ==> ={res} ].
proof strict.
transitivity S1_left.sample_dh_real (true ==> ={res}) (true ==> ={res}) => //.
- by conseq Eq_Sample_DH_S1_left.
transitivity S1_right.sample_dh_real (true ==> ={res}) (true ==> ={res}) => //.
- by conseq Eq_S1_left_S1_right.
transitivity S2_left.sample_dh_real (true ==> ={res}) (true ==> ={res}) => //.
- by conseq Eq_S1_right_S2_left.
transitivity S2_right.sample_dh_real (true ==> ={res}) (true ==> ={res}) => //.
- by conseq Eq_S2_left_S2_right.
by conseq Eq_S2_right_Sample_DH_distr.
qed.

lemma Eq_DDH_real_distr:
  forall (D <: DDH_DISTINGUISHER {-DDH_real, -DDH_distr_real}),
    equiv[ DDH_real(D).main ~ DDH_distr_real(D).main :
           ={glob D,i} ==> ={res} ].
proof strict.
  move=> D.
  proc. call (_ : true). call Eq_Sample_DH_distr_real. skip; smt.
qed.

lemma Eq_DDH_random_distr:
  forall (D <: DDH_DISTINGUISHER {-DDH_real, -DDH_distr_real}),
    equiv[ DDH_random(D).main ~ DDH_distr_random(D).main :
           ={glob D, i} ==> ={res} ].
proof strict.
  move=> D.
  proc. call (_ : true). call Eq_Sample_DH_distr_random. skip; smt.
qed.
