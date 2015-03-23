(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

require import Int.
require import Real.
require import FSet.
require import ISet.
require import Pair.
require import Distr.
require import Monoid.
require import SampleBool.
require Hybrid.

type input.

clone import Hybrid as H 
  with type input <- input * input,
       type outputA <- bool.

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
    r = O.orcl(m0);
    C.incr();
    return r;
  }
}.

module OrclR (O:Orcl) = {
  proc orcl (m0 m1:input) : output = {
    var r : output;
    C.incr();
    r = O.orcl(m1);
    return r;
  }
}.

module Orclb (O:Orcl) = {

  var b:bool
  proc orcl (m0 m1:input) : output = {
    var r : output;
    C.incr();
    r = O.orcl(b?m0:m1);
    return r;
  }
}.

module type Adv (O:Orcl, LR:LR) = { proc main():bool { O.leaks O.orcl LR.orcl }}.

module INDL (O:Orcl, A:Adv) = {
  module A = A(O,OrclL(O))
  proc main():bool = {
    var b' : bool;
    C.init();
    b' = A.main();
    return b';
  }
}.

module INDR (O:Orcl, A:Adv) = {
  module A = A(O,OrclR(O))
  proc main():bool = {
    var b' : bool;
    C.init();
    b' = A.main();
    return b';
  }
}.

module INDb(O:Orcl,A:Adv) = {
  module A = A(O,Orclb(O))
  proc main():bool = {
    var b' : bool;
    C.init();
    Orclb.b = ${0,1};
    b' = A.main();
    return Orclb.b = b';
  }
}.

(* We prove the equivalence between the two usual definitions *)
(* i.e (INDb - 1/2) = (INDL - INDR)/2 *)

section.
  declare module O:Orcl {C, Orclb}.
  declare module A:Adv  {C, O, Orclb}.

  local module WA = {
    module A=A(O,Orclb(O))  
    proc work(x:bool) : bool = {
      var b' : bool;
      C.init();
      Orclb.b = x;
      b' = A.main();
      return b';
    }
  }.

  lemma INDb_INDLR &m (p:glob A -> glob O -> int -> bool):
     Pr[INDb(O,A).main() @ &m : res /\ p (glob A) (glob O) C.c] -
       Pr[INDR(O,A).main() @ &m : p (glob A) (glob O) C.c]/2%r =
     (Pr[INDL(O,A).main() @ &m : res /\ p (glob A) (glob O) C.c] -
      Pr[INDR(O,A).main() @ &m : res /\ p (glob A) (glob O) C.c])/2%r.
  proof strict.
   cut := Sample_bool WA &m 
     (fun (g:glob WA), let (b,c,go,ga) = g in p ga go c) => /= H.
   cut -> : Pr[INDb(O, A).main() @ &m : res /\ p (glob A) (glob O) C.c] =
    Pr[MB.M.Rand(WA).main() @ &m : fst res = snd res /\ p (glob A) (glob O) C.c].
     byequiv (_: ={glob A,glob O} ==> ={glob A,glob O, C.c} /\
                   res{1} = (fst res = snd res){2}) => //;proc.
     inline C.init WA.work;simplify fst snd. 
     by swap{1} 2 -1; sim; proc (={Orclb.b, C.c}).
   cut He: equiv [INDR(O, A).main ~ WA.work: x{2}=false /\ 
                   ={glob A,glob O} ==> ={res,glob A,glob O, C.c}].
    proc. 
    call (_: ={glob O, C.c} /\ Orclb.b{2} = false).
      by proc (={C.c} /\ Orclb.b{2} = false).      
      by proc (={C.c} /\ Orclb.b{2} = false). 
      by proc;inline C.incr;wp;call(_:true);wp;skip;progress.
    inline C.init;by wp.
   cut -> : Pr[INDR(O, A).main() @ &m : p (glob A) (glob O) C.c] =
            Pr[WA.work(false) @ &m : p (glob A) (glob O) C.c].
     by byequiv He.
   cut -> : Pr[INDR(O, A).main() @ &m : res /\ p (glob A) (glob O) C.c] = 
            Pr[WA.work(false) @ &m : res /\ p (glob A) (glob O) C.c].
     by byequiv He.
   (cut -> : Pr[INDL(O, A).main() @ &m : res /\ p (glob A) (glob O) C.c] = 
            Pr[WA.work(true) @ &m : res /\ p (glob A) (glob O) C.c]) => //.
   byequiv 
      (_: x{2}=true /\ ={glob A,glob O} ==> ={res,glob A,glob O, C.c}) => //.
   proc; call (_: ={glob O, C.c} /\ Orclb.b{2} = true).
     by proc (={C.c} /\ Orclb.b{2} = true).      
     by proc (={C.c} /\ Orclb.b{2} = true). 
     by proc;inline C.incr;wp;call(_:true);wp;skip;progress.
   inline C.init;by wp.
 qed.

end section.

(* We prove that IND-n is equivalent to IND-1 *)

module Orcl2(O:Orcl) = {
  proc leaks (il:inleaks) : outleaks = {
    var r : outleaks;
    r = O.leaks(il);
    return r;
  }

  proc orcl1 (m:input * input) : output = {
    var r : output;
    r = O.orcl(fst m);
    return r;
  }

  proc orcl2 (m:input * input) : output = {
    var r : output;
    r = O.orcl(snd m);
    return r;
  }  
}.

module LRB2 (O:Orcl,LR:LR) = {
  proc orcl(m0 m1:input):output = {
    var r : output;
    if (LRB.l0 < LRB.l) r = O.orcl(m0);
    else { 
      if (LRB.l0 = LRB.l) r = LR.orcl(m0,m1);
      else r = O.orcl(m1);
    }
    LRB.l = LRB.l + 1;
    return r;
  }    
}.

module B(A:Adv, O:Orcl, LR:LR) = {
  module A = A(O,LRB2(O,LR))
  proc main():bool = {
    var b':bool;
    LRB.l0 = $[0..q-1];
    LRB.l  = 0;
    b' = A.main();
    return b';
  }
}.

section.

  declare module O:Orcl {C, LRB}.
  declare module A:Adv  {C, O, LRB}.

  local module A' (Ob:Orclb, LR:H.Orcl) = {
    module O = {
      proc leaks(il:inleaks) : outleaks = {
        var r : outleaks;
        r = Ob.leaks(il);
        return r;
      }
      proc orcl(m:input) : output = {
        var r:output;
        r = Ob.orcl1((m,m));
        return r;
      }
    }
    module LR' = {
      proc orcl (m0 m1:input) : output = {
        var r : output;
        r = LR.orcl((m0,m1));
        return r;
      }
    }
    module A = A(O,LR')
    proc main():bool = {
      var b':bool;
      b' = A.main();
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
     Pr[INDL(O,B(A)).main() @ &m : res /\ p (glob A) (glob O) LRB.l /\
                                    LRB.l <= q /\ C.c <= 1] - 
       Pr[INDR(O,B(A)).main() @ &m : res /\ p (glob A) (glob O) LRB.l /\
                                    LRB.l <= q /\ C.c <= 1]  =
     1%r/q%r * (
       Pr[INDL(O,A).main() @ &m : res /\ p (glob A) (glob O) C.c /\
                                  C.c <= q] - 
         Pr[INDR(O,A).main() @ &m :  res /\ p (glob A) (glob O) C.c /\
                                  C.c <= q]).
  proof -strict.
    cut := Hybrid (Orcl2(O)) A' _ _ _ _ &m (fun ga go c b, b /\ p ga go c).
      by proc;call losslessL.
      by proc;call losslessO.
      by proc;call losslessO.
      intros Ob LR Hlr Hl Ho1 Ho2;proc.
      by call (losslessA (<:A'(Ob,LR).O) (<:A'(Ob,LR).LR') _ _ _) => //;proc;
        [call Hlr | call Hl | call Ho1].
    zeta beta => H.
    cut -> : Pr[INDL(O, B(A)).main() @ &m :
                 res /\ p (glob A) (glob O) LRB.l /\ LRB.l <= q /\ C.c <= 1] =
             Pr[Ln(Orcl2(O), H.B(A')).main() @ &m :
                 ((res /\ p (glob A) (glob O) LRB.l) /\ LRB.l <= q) /\ C.c <= 1].
      byequiv (_: ={glob A,glob O} ==>
                     ={res,glob A,glob O,glob LRB, C.c}) => //;proc.
      call (_: ={glob A,glob O, C.c} ==> ={glob A,glob O,glob LRB,C.c,res}).
        proc;inline H.B(A', Orcl2(O), Orclc(L(Orcl2(O)))).A.main;wp.
        call (_: ={glob O, C.c, glob LRB}).
          proc *. inline A'(Orcl2(O), LRB(Orcl2(O), Orclc(L(Orcl2(O))))).O.leaks Orcl2(O).leaks;wp.
          by call (_:true);wp.
          proc *. inline A'(Orcl2(O), LRB(Orcl2(O), Orclc(L(Orcl2(O))))).O.orcl Orcl2(O).orcl1;wp.
          by call (_:true);wp.
          proc. inline LRB(Orcl2(O), Orclc(L(Orcl2(O)))).orcl Orcl2(O).orcl1 Orcl2(O).orcl2;wp.
          sp;if => //;first by wp;call (_:true);wp.
          if => //;last by wp;call (_:true);wp.
          inline OrclL(O).orcl Orclc(L(Orcl2(O))).orcl L(Orcl2(O)).orcl Orcl2(O).orcl1 C.incr.
          by wp;call (_: true);wp.
        by wp;rnd.
      by call (_:true ==> ={C.c});first by proc;wp.
    cut -> : Pr[INDR(O, B(A)).main() @ &m :
                 res /\ p (glob A) (glob O) LRB.l /\ LRB.l <= q /\ C.c <= 1] =
             Pr[Rn(Orcl2(O), H.B(A')).main() @ &m :
                 ((res /\ p (glob A) (glob O) LRB.l) /\ LRB.l <= q) /\ C.c <= 1].
      byequiv (_: ={glob A,glob O} ==>
                     ={res,glob A,glob O,glob LRB, C.c}) => //;proc.
      call (_: ={glob A,glob O, C.c} ==> ={glob A,glob O,glob LRB,C.c,res}).
        proc;inline H.B(A', Orcl2(O), Orclc(R(Orcl2(O)))).A.main;wp.
        call (_: ={glob O, C.c, glob LRB}).
          proc *. inline A'(Orcl2(O), LRB(Orcl2(O), Orclc(R(Orcl2(O))))).O.leaks Orcl2(O).leaks;wp.
          by call (_:true);wp.
          proc *. inline A'(Orcl2(O), LRB(Orcl2(O), Orclc(R(Orcl2(O))))).O.orcl Orcl2(O).orcl1;wp.
          by call (_:true);wp.
          proc. inline LRB(Orcl2(O), Orclc(R(Orcl2(O)))).orcl Orcl2(O).orcl1 Orcl2(O).orcl2;wp.
          sp;if => //;first by wp;call (_:true);wp.
          if => //;last by wp;call (_:true);wp.
          inline OrclR(O).orcl Orclc(R(Orcl2(O))).orcl R(Orcl2(O)).orcl Orcl2(O).orcl2 C.incr.
          by wp;call (_: true);wp.
        by wp;rnd.
      by call (_:true ==> ={C.c});first by proc;wp.
   (* BUG : rewrite H.  *)
   cut -> : Pr[INDL(O, A).main() @ &m : res /\ p (glob A) (glob O) C.c /\ C.c <= q] =
            Pr[Ln(Orcl2(O), A').main() @ &m : (res /\ p (glob A) (glob O) C.c) /\ C.c <= q].
     byequiv (_: ={glob A,glob O} ==>
                    ={res,glob A,glob O, C.c}) => //;proc.
      call (_: ={glob A,glob O, C.c} ==> ={glob A,glob O,C.c,res}).
        proc *. inline A'(Orcl2(O), Orclc(L(Orcl2(O)))).main;sim.
        call (_: ={glob O, C.c}) => //.
          proc *. inline A'(Orcl2(O), Orclc(L(Orcl2(O)))).O.leaks Orcl2(O).leaks;wp.
          by call (_:true);wp.
          proc *. inline A'(Orcl2(O), Orclc(L(Orcl2(O)))).O.orcl Orcl2(O).orcl1;wp.
          by call (_:true);wp.
          proc;inline Orclc(L(Orcl2(O))).orcl L(Orcl2(O)).orcl Orcl2(O).orcl1 C.incr.
        by wp;call(_:true);wp.
      by call (_:true ==> ={C.c});first by proc;wp.
   cut -> : Pr[INDR(O, A).main() @ &m : res /\ p (glob A) (glob O) C.c /\ C.c <= q] =
            Pr[Rn(Orcl2(O), A').main() @ &m : (res /\ p (glob A) (glob O) C.c) /\ C.c <= q].
     byequiv (_: ={glob A,glob O} ==>
                    ={res,glob A,glob O, C.c}) => //;proc.
      call (_: ={glob A,glob O, C.c} ==> ={glob A,glob O,C.c,res}).
        proc *. inline A'(Orcl2(O), Orclc(R(Orcl2(O)))).main;sim.
        call (_: ={glob O, C.c}) => //.
          proc *. inline A'(Orcl2(O), Orclc(R(Orcl2(O)))).O.leaks Orcl2(O).leaks;wp.
          by call (_:true);wp.
          proc *. inline A'(Orcl2(O), Orclc(R(Orcl2(O)))).O.orcl Orcl2(O).orcl1;wp.
          by call (_:true);wp.
          proc;inline Orclc(R(Orcl2(O))).orcl R(Orcl2(O)).orcl Orcl2(O).orcl2 C.incr.
        by wp;call(_:true);wp.
      by call (_:true ==> ={C.c});first by proc;wp.
    apply H.
  qed.

end section.

