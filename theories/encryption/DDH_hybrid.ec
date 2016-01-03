(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Real.
require import Int IntDiv.
require import Prime_field.
require import Cyclic_group_prime.

require Hybrid.

op n : int.
clone Hybrid as H with
  type input <- unit,
  type output <- group * group * group,
  type inleaks <- unit,
  type outleaks <- unit,
  type outputA <- bool,
  op q <- n.
import H.

module DDHl = {
  proc orcl () : group * group * group = {
    var x, y: gf_q;
    x <$ Dgf_q.dgf_q;
    y <$ Dgf_q.dgf_q;
    return (g^x, g^y, g^(x * y));
  }
}.

module DDHr = {
  proc orcl () : group * group * group = {
    var x, y, z: gf_q;
    x <$ Dgf_q.dgf_q;
    y <$ Dgf_q.dgf_q;
    z <$ Dgf_q.dgf_q;
    return (g^x, g^y, g^z);
  }
}.

module DDHb : H.Orclb = {
  proc leaks () : unit = { }
  proc orclL = DDHl.orcl
  proc orclR = DDHr.orcl
}.

lemma islossless_leaks : islossless DDHb.leaks.
proof. proc;auto. qed.

lemma islossless_orcl1 : islossless DDHb.orclL.
proof. proc;auto;progress;smt. qed.

lemma islossless_orcl2 : islossless DDHb.orclR.
proof. proc;auto;progress;smt. qed.

section.

  declare module A : H.AdvOrclb{Count,HybOrcl,DDHb}.

  axiom losslessA : forall (Ob0 <: Orclb{A}) (LR <: Orcl{A}),
    islossless LR.orcl =>
    islossless Ob0.leaks =>
    islossless Ob0.orclL =>
    islossless Ob0.orclR => islossless A(Ob0, LR).main.
 
  lemma Hybrid:
    forall &m,
      Pr[Ln(DDHb, HybGame(A)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1 ] -
      Pr[Rn(DDHb, HybGame(A)).main() @ &m : (res /\ HybOrcl.l <= n) /\ Count.c <= 1 ] = 
      1%r / n%r *
       (Pr[Ln(DDHb, A).main() @ &m : (res /\ Count.c <= n) ] -
        Pr[Rn(DDHb, A).main() @ &m : (res /\ Count.c <= n) ]).
  proof.
   move=> &m.
   apply (H.Hybrid (<:DDHb) (<:A) _ _ _ _ &m 
       (fun (ga:glob A) (gb:glob DDHb) (c:int) (r:bool), r)).
   apply islossless_leaks. apply islossless_orcl1. apply islossless_orcl2. apply losslessA.
  qed.

end section.
