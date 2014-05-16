require import Real.
require import Int.
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
    x = $ Dgf_q.dgf_q;
    y = $ Dgf_q.dgf_q;
    return (g^x, g^y, g^(x * y));
  }
}.

module DDHr = {
  proc orcl () : group * group * group = {
    var x, y, z: gf_q;
    x = $ Dgf_q.dgf_q;
    y = $ Dgf_q.dgf_q;
    z = $ Dgf_q.dgf_q;
    return (g^x, g^y, g^z);
  }
}.

module DDHb : H.Orclb = {
  proc leaks () : unit = { }
  proc orcl1 = DDHl.orcl
  proc orcl2 = DDHr.orcl
}.

lemma islossless_leaks : islossless DDHb.leaks.
proof. proc;auto. qed.

lemma islossless_orcl1 : islossless DDHb.orcl1.
proof. proc;auto;progress;smt. qed.

lemma islossless_orcl2 : islossless DDHb.orcl2.
proof. proc;auto;progress;smt. qed.

section.

  declare module A : H.OrclbAdv{C,LRB,DDHb}. 

  axiom losslessA : forall (Ob0 <: Orclb{A}) (LR <: Orcl{A}),
    islossless LR.orcl =>
    islossless Ob0.leaks =>
    islossless Ob0.orcl1 =>
    islossless Ob0.orcl2 => islossless A(Ob0, LR).main.
 
  lemma Hybrid:
    forall &m,
      Pr[Ln(DDHb, B(A)).main(tt) @ &m : (res /\ LRB.l <= n) /\ C.c <= 1 ] -
      Pr[Rn(DDHb, B(A)).main(tt) @ &m : (res /\ LRB.l <= n) /\ C.c <= 1 ] = 
      1%r / n%r *
       (Pr[Ln(DDHb, A).main(tt) @ &m : (res /\ C.c <= n) ] -
        Pr[Rn(DDHb, A).main(tt) @ &m :  (res /\ C.c <= n) ]).
  proof. 
   intros &m.
   apply (H.Hybrid (<:DDHb) (<:A) _ _ _ _ &m 
       (fun (ga:glob A) (gb:glob DDHb) (c:int) (r:bool), r)).
   apply islossless_leaks. apply islossless_orcl1. apply islossless_orcl2. apply losslessA.
  qed.

end section.