(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore FSet Distr SampleBool OldMonoid.
require DBool Hybrid.

type input.

clone import Hybrid as H
  with type input <- input * input,
       type outputA <- bool.

(* Specialize Hybrid argument to oracle that takes
   two arguments and either uses first argument (left)
   or second argument (right). *)

module type Orcl = {
  proc leaks (il:inleaks) : outleaks
  proc orcl (m:input) : output
}.

module type LR = {
  proc orcl (m0 m1:input) : output
}.

module OrclL (O:Orcl) = {

  proc orcl (m0 m1:input) : output = {
    var r : output;
    r <@ O.orcl(m0);
    Count.incr();
    return r;
  }
}.

module OrclR (O:Orcl) = {
  proc orcl (m0 m1:input) : output = {
    var r : output;
    Count.incr();
    r <@ O.orcl(m1);
    return r;
  }
}.

module type Adv (O:Orcl, LR:LR) = {
  proc main():bool { O.leaks O.orcl LR.orcl }
}.

module INDL (O:Orcl, A:Adv) = {
  module A = A(O,OrclL(O))
  proc main():bool = {
    var b' : bool;
    Count.init();
    b' <@ A.main();
    return b';
  }
}.

module INDR (O:Orcl, A:Adv) = {
  module A = A(O,OrclR(O))
  proc main():bool = {
    var b' : bool;
    Count.init();
    b' <@ A.main();
    return b';
  }
}.

(* -------------------------------------------------------------------- *)
(* We prove that IND-n is equivalent to IND-1 *)

module Orcl2(O:Orcl) = {
  proc leaks = O.leaks

  proc orclL(m : input * input) : output = {
    var r;
    r <@ O.orcl(fst m);
    return r;
  }

  proc orclR(m : input * input) : output = {
    var r;
    r <@ O.orcl(snd m);
    return r;
  }
}.

module HybOrcl2 (O:Orcl,LR:LR) = {
  proc orcl(m0 m1:input):output = {
    var r : output;
    if   (HybOrcl.l0 < HybOrcl.l) r <@ O.orcl(m0);
    elif (HybOrcl.l0 = HybOrcl.l) r <@ LR.orcl(m0,m1);
    else                          r <@ O.orcl(m1);
    HybOrcl.l <- HybOrcl.l + 1;
    return r;
  }
}.

module HybGame2(A:Adv, O:Orcl, LR:LR) = {
  module A = A(O,HybOrcl2(O,LR))
  proc main():bool = {
    var b':bool;
    HybOrcl.l0 <$ [0..q-1];
    HybOrcl.l  <- 0;
    b'         <@ A.main();
    return b';
  }
}.

section.

  declare module O:Orcl {Count, HybOrcl}.
  declare module A:Adv  {Count, O, HybOrcl}.

  local module A' (Ob : Orclb, LR : H.Orcl) = {
    module O = {
      proc leaks = Ob.leaks

      proc orcl(m:input) : output = {
        var r : output;
        r <@ Ob.orclL((m,m));
        return r;
      }
    }
    module LR' = {
      proc orcl (m0 m1:input) : output = {
        var r : output;
        r <@ LR.orcl((m0,m1));
        return r;
      }
    }
    module A = A(O,LR')
    proc main() : bool = {
      var b' : bool;
      b' <@ A.main();
      return b';
    }
  }.

  axiom losslessL: islossless O.leaks.
  axiom losslessO: islossless O.orcl.
  axiom losslessA (O <: Orcl{A}) (LR <: LR{A}):
    islossless LR.orcl =>
    islossless O.leaks => islossless O.orcl =>
    islossless A(O, LR).main.
  axiom q_pos : 0 < q.

  lemma IND1_INDn &m (p:glob A -> glob O -> int -> bool):
     Pr[INDL(O,HybGame2(A)).main() @ &m : res /\ p (glob A) (glob O) HybOrcl.l /\
                                          HybOrcl.l <= q /\ Count.c <= 1] -
       Pr[INDR(O,HybGame2(A)).main() @ &m : res /\ p (glob A) (glob O) HybOrcl.l /\
                                            HybOrcl.l <= q /\ Count.c <= 1]  =
     1%r/q%r * (
       Pr[INDL(O,A).main() @ &m : res /\ p (glob A) (glob O) Count.c /\
                                  Count.c <= q] -
         Pr[INDR(O,A).main() @ &m :  res /\ p (glob A) (glob O) Count.c /\
                                     Count.c <= q]).
  proof.
    cut := Hybrid (Orcl2(O)) A' _ _ _ _ &m (fun ga go c b, b /\ p ga go c).
      by apply losslessL.
      by proc;call losslessO.
      by proc;call losslessO.
      move=> Ob LR Hlr Hl Ho1 Ho2;proc.
      call (losslessA (<:A'(Ob,LR).O) (<:A'(Ob,LR).LR') _ _ _) => //;proc.
        by call Hlr. by call Ho1.
    zeta beta => H.
    cut -> : Pr[INDL(O, HybGame2(A)).main() @ &m :
                 res /\ p (glob A) (glob O) HybOrcl.l /\ HybOrcl.l <= q /\ Count.c <= 1] =
             Pr[Ln(Orcl2(O), H.HybGame(A')).main() @ &m :
                 ((res /\ p (glob A) (glob O) HybOrcl.l) /\ HybOrcl.l <= q) /\ Count.c <= 1].
      byequiv (_: ={glob A,glob O} ==>
                     ={res,glob A,glob O,glob HybOrcl, Count.c}) => //;proc.
      call (_: ={glob A,glob O, Count.c} ==> ={glob A,glob O,glob HybOrcl,Count.c,res}).
        proc;inline H.HybGame(A', Orcl2(O), OrclCount(L(Orcl2(O)))).A.main;wp.
        call (_: ={glob O, Count.c, glob HybOrcl}).
          proc *. wp.
          by call (_:true);wp.
          proc *. inline A'(Orcl2(O), HybOrcl(Orcl2(O), OrclCount(L(Orcl2(O))))).O.orcl Orcl2(O).orclL;wp.
          by call (_:true);wp.
          proc. inline HybOrcl(Orcl2(O), OrclCount(L(Orcl2(O)))).orcl Orcl2(O).orclL Orcl2(O).orclR;wp.
          sp;if => //;first by wp;call (_:true);wp.
          if => //;last by wp;call (_:true);wp.
          inline OrclL(O).orcl OrclCount(L(Orcl2(O))).orcl L(Orcl2(O)).orcl Orcl2(O).orclL Count.incr.
          by wp;call (_: true);wp.
        by wp;rnd.
      by call (_:true ==> ={Count.c});first by proc;wp.
    cut -> : Pr[INDR(O, HybGame2(A)).main() @ &m :
                 res /\ p (glob A) (glob O) HybOrcl.l /\ HybOrcl.l <= q /\ Count.c <= 1] =
             Pr[Rn(Orcl2(O), H.HybGame(A')).main() @ &m :
                 ((res /\ p (glob A) (glob O) HybOrcl.l) /\ HybOrcl.l <= q) /\ Count.c <= 1].
      byequiv (_: ={glob A,glob O} ==>
                     ={res,glob A,glob O,glob HybOrcl, Count.c}) => //;proc.
      call (_: ={glob A,glob O, Count.c} ==> ={glob A,glob O,glob HybOrcl,Count.c,res}).
        proc;inline H.HybGame(A', Orcl2(O), OrclCount(R(Orcl2(O)))).A.main;wp.
        call (_: ={glob O, Count.c, glob HybOrcl}).
          proc *. wp.
          by call (_:true);wp.
          proc *. inline A'(Orcl2(O), HybOrcl(Orcl2(O), OrclCount(R(Orcl2(O))))).O.orcl Orcl2(O).orclL;wp.
          by call (_:true);wp.
          proc. inline HybOrcl(Orcl2(O), OrclCount(R(Orcl2(O)))).orcl Orcl2(O).orclL Orcl2(O).orclR;wp.
          sp;if => //;first by wp;call (_:true);wp.
          if => //;last by wp;call (_:true);wp.
          inline OrclR(O).orcl OrclCount(R(Orcl2(O))).orcl R(Orcl2(O)).orcl Orcl2(O).orclR Count.incr.
          by wp;call (_: true);wp.
        by wp;rnd.
      by call (_:true ==> ={Count.c});first by proc;wp.
   (* BUG : rewrite H.  *)
   cut -> : Pr[INDL(O, A).main() @ &m : res /\ p (glob A) (glob O) Count.c /\ Count.c <= q] =
            Pr[Ln(Orcl2(O), A').main() @ &m : (res /\ p (glob A) (glob O) Count.c) /\ Count.c <= q].
     byequiv (_: ={glob A,glob O} ==>
                    ={res,glob A,glob O, Count.c}) => //;proc.
      call (_: ={glob A,glob O, Count.c} ==> ={glob A,glob O,Count.c,res}).
        proc *. inline A'(Orcl2(O), OrclCount(L(Orcl2(O)))).main;sim.
        call (_: ={glob O, Count.c}) => //.
          proc *. wp.
          by call (_:true);wp.
          proc *. inline A'(Orcl2(O), OrclCount(L(Orcl2(O)))).O.orcl Orcl2(O).orclL;wp.
          by call (_:true);wp.
          proc;inline OrclCount(L(Orcl2(O))).orcl L(Orcl2(O)).orcl Orcl2(O).orclL Count.incr.
        by wp;call(_:true);wp.
      by call (_:true ==> ={Count.c});first by proc;wp.
   cut -> : Pr[INDR(O, A).main() @ &m : res /\ p (glob A) (glob O) Count.c /\ Count.c <= q] =
            Pr[Rn(Orcl2(O), A').main() @ &m : (res /\ p (glob A) (glob O) Count.c) /\ Count.c <= q].
     byequiv (_: ={glob A,glob O} ==>
                    ={res,glob A,glob O, Count.c}) => //;proc.
      call (_: ={glob A,glob O, Count.c} ==> ={glob A,glob O,Count.c,res}).
        proc *. inline A'(Orcl2(O), OrclCount(R(Orcl2(O)))).main;sim.
        call (_: ={glob O, Count.c}) => //.
          proc *. wp.
          by call (_:true);wp.
          proc *. inline A'(Orcl2(O), OrclCount(R(Orcl2(O)))).O.orcl Orcl2(O).orclL;wp.
          by call (_:true);wp.
          proc;inline OrclCount(R(Orcl2(O))).orcl R(Orcl2(O)).orcl Orcl2(O).orclR Count.incr.
        by wp;call(_:true);wp.
      by call (_:true ==> ={Count.c});first by proc;wp.
    apply H.
  qed.

end section.

(* -------------------------------------------------------------------- *)
(* We now prove the equivalence between the two usual definitions *)
(* i.e (INDb - 1/2) = (INDL - INDR)/2 *)

module Orclb (O:Orcl) = {

  var b:bool
  proc orcl (m0 m1:input) : output = {
    var r : output;
    Count.incr();
    r <@ O.orcl(b?m0:m1);
    return r;
  }
}.

module INDb(O:Orcl,A:Adv) = {
  module A = A(O,Orclb(O))
  proc main():bool = {
    var b' : bool;
    Count.init();
    Orclb.b <$ {0,1};
    b' <@ A.main();
    return Orclb.b = b';
  }
}.

section.
  declare module O:Orcl {Count, Orclb}.
  declare module A:Adv  {Count, O, Orclb}.

  local module WA = {
    module A = A(O,Orclb(O))
    proc work(x : bool) : bool = {
      var b' : bool;
      Count.init();
      Orclb.b <- x;
      b' <@ A.main();
      return b';
    }
  }.

  lemma INDb_INDLR &m (p:glob A -> glob O -> int -> bool):
     Pr[INDb(O,A).main() @ &m : res /\ p (glob A) (glob O) Count.c] -
       Pr[INDR(O,A).main() @ &m : p (glob A) (glob O) Count.c]/2%r =
     (Pr[INDL(O,A).main() @ &m : res /\ p (glob A) (glob O) Count.c] -
      Pr[INDR(O,A).main() @ &m : res /\ p (glob A) (glob O) Count.c])/2%r.
  proof.
   cut := Sample_bool WA &m
     (fun (g:glob WA), let (b,c,ga,go) = g in p ga go c) => /= H.
   cut -> : Pr[INDb(O, A).main() @ &m : res /\ p (glob A) (glob O) Count.c] =
    Pr[MB.M.Rand(WA).main() @ &m : fst res = snd res /\ p (glob A) (glob O) Count.c].
     byequiv (_: ={glob A,glob O} ==> ={glob A,glob O, Count.c} /\
                   res{1} = (fst res = snd res){2}) => //;proc.
     inline Count.init WA.work;simplify fst snd.
     by swap{1} 2 -1; sim; proc (={Orclb.b, Count.c}).
   cut He: equiv [INDR(O, A).main ~ WA.work: x{2}=false /\
                   ={glob A,glob O} ==> ={res,glob A,glob O, Count.c}].
    proc.
    call (_: ={glob O, Count.c} /\ Orclb.b{2} = false).
      by proc (={Count.c} /\ Orclb.b{2} = false).
      by proc (={Count.c} /\ Orclb.b{2} = false).
      by proc;inline Count.incr;wp;call(_:true);wp;skip;progress.
    inline Count.init;by wp.
   cut -> : Pr[INDR(O, A).main() @ &m : p (glob A) (glob O) Count.c] =
            Pr[WA.work(false) @ &m : p (glob A) (glob O) Count.c].
     by byequiv He.
   cut -> : Pr[INDR(O, A).main() @ &m : res /\ p (glob A) (glob O) Count.c] =
            Pr[WA.work(false) @ &m : res /\ p (glob A) (glob O) Count.c].
     by byequiv He.
   (cut -> : Pr[INDL(O, A).main() @ &m : res /\ p (glob A) (glob O) Count.c] =
            Pr[WA.work(true) @ &m : res /\ p (glob A) (glob O) Count.c]) => //.
   byequiv
      (_: x{2}=true /\ ={glob A,glob O} ==> ={res,glob A,glob O, Count.c}) => //.
   proc; call (_: ={glob O, Count.c} /\ Orclb.b{2} = true).
     by proc (={Count.c} /\ Orclb.b{2} = true).
     by proc (={Count.c} /\ Orclb.b{2} = true).
     by proc;inline Count.incr;wp;call(_:true);wp;skip;progress.
   inline Count.init;by wp.
 qed.

end section.
