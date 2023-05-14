require import Real.
require import Int IntDiv.

require import Group.

clone CyclicGroup as G.

axiom prime_p : IntDiv.prime G.order.

clone G.PowZMod as GP with
  lemma prime_order <- prime_p.

clone GP.FDistr as FD.

(* Cloning GP.ZModE duplicates the type exp and leads to ambiguities. *)
(* clone GP.ZModE as ZP. *) 

import G GP FD GP.ZModE.

require Hybrid.

op n : { int | 0 < n } as n_pos.
clone import Hybrid as H with
  type input <- unit,
  type output <- group * group * group,
  type inleaks <- unit,
  type outleaks <- unit,
  type outputA <- bool,
  op q <- n
  proof* by smt(n_pos).

module DDHl = {
  proc orcl () : group * group * group = {
    var x, y: exp;
    x <$ FD.dt;
    y <$ FD.dt;
    return (g ^ x, g ^ y, g ^ (x * y));
  }
}.

module DDHr = {
  proc orcl () : group * group * group = {
    var x, y, z: exp;
    x <$ FD.dt;
    y <$ FD.dt;
    z <$ FD.dt;
    return (g ^ x, g ^ y, g ^ z);
  }
}.

module DDHb : H.Orclb = {
  proc leaks () : unit = { }
  proc orclL = DDHl.orcl
  proc orclR = DDHr.orcl
}.

lemma islossless_leaks : islossless DDHb.leaks
  by proc; auto.

lemma islossless_orcl1 : islossless DDHb.orclL
  by proc; auto; progress; smt.

lemma islossless_orcl2 : islossless DDHb.orclR
  by proc; auto; progress; smt.

section.

  declare module A <: H.AdvOrclb{-Count,-HybOrcl,-DDHb}.

  declare axiom losslessA : forall (Ob0 <: Orclb{-A}) (LR <: Orcl{-A}),
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
   apply (H.Hybrid_div (<:DDHb) (<:A) _ _ _ _ &m
       (fun (ga:glob A) (gb:glob DDHb) (c:int) (r:bool), r)).
   apply islossless_leaks. apply islossless_orcl1. apply islossless_orcl2. apply losslessA.
   smt(n_pos).
  qed.

end section.
