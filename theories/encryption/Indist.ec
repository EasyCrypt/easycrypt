require import AllCore FSet Distr SampleBool.
require DBool Hybrid.

type input.

clone import Hybrid as H with
  type input <- input * input,
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

module type Adv (O : Orcl) (LR : LR) = {
  proc main(): bool { O.leaks, O.orcl, LR.orcl }
}.

module INDL (O : Orcl) (A : Adv) = {
  proc main():bool = {
    var b' : bool;

    Count.init();
    b' <@ A(O, OrclL(O)).main();
    return b';
  }
}.

module INDR (O : Orcl) (A : Adv) = {
  proc main():bool = {
    var b' : bool;

    Count.init();
    b' <@ A(O,OrclR(O)).main();
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

module HybOrcl2 (O:Orcl) (LR:LR) = {
  proc orcl(m0 m1:input):output = {
    var r : output;

    if   (HybOrcl.l0 < HybOrcl.l) r <@ O.orcl(m0);
    elif (HybOrcl.l0 = HybOrcl.l) r <@ LR.orcl(m0,m1);
    else                          r <@ O.orcl(m1);
    HybOrcl.l <- HybOrcl.l + 1;
    return r;
  }
}.

module HybGame2(A:Adv) (O:Orcl) (LR:LR) = {
  proc main():bool = {
    var b':bool;

    HybOrcl.l0 <$ [0..max 0 (q-1)];
    HybOrcl.l  <- 0;
    b'         <@ A(O,HybOrcl2(O,LR)).main();
    return b';
  }
}.

section.
declare module O <: Orcl {-Count, -HybOrcl}.
declare module A <: Adv  {-Count, -O, -HybOrcl}.

declare axiom losslessL: islossless O.leaks.
declare axiom losslessO: islossless O.orcl.
declare axiom losslessA (O <: Orcl{-A}) (LR <: LR{-A}):
  islossless LR.orcl =>
  islossless O.leaks => islossless O.orcl =>
  islossless A(O, LR).main.

declare axiom q_pos : 0 < q.

local module A' (Ob : Orclb) (LR : H.Orcl) = {
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

  proc main() : bool = {
    var b' : bool;

    b' <@ A(O, LR').main();
    return b';
  }
}.

lemma IND1_INDn &m (p:glob A -> glob O -> int -> bool):
      Pr[INDL(O,HybGame2(A)).main() @ &m:
              res /\ p (glob A) (glob O) HybOrcl.l
           /\ HybOrcl.l <= q /\ Count.c <= 1]
    - Pr[INDR(O,HybGame2(A)).main() @ &m:
              res /\ p (glob A) (glob O) HybOrcl.l
           /\ HybOrcl.l <= q /\ Count.c <= 1]
  = 1%r/q%r * (  Pr[INDL(O,A).main() @ &m:
                         res /\ p (glob A) (glob O) Count.c /\ Count.c <= q]
               - Pr[INDR(O,A).main() @ &m:
                         res /\ p (glob A) (glob O) Count.c /\ Count.c <= q]).
proof.
have ->:   Pr[INDL(O, HybGame2(A)).main() @ &m:
                res /\ p (glob A) (glob O) HybOrcl.l /\ HybOrcl.l <= q /\ Count.c <= 1]
         = Pr[Ln(Orcl2(O), H.HybGame(A')).main() @ &m :
                ((res /\ p (glob A) (glob O) HybOrcl.l) /\ HybOrcl.l <= q) /\ Count.c <= 1].
+ byequiv (: ={glob A,glob O}
             ==> ={res,glob A,glob O,glob HybOrcl, Count.c})=> //.
  proc.
  call (: ={glob A,glob O, Count.c} ==> ={glob A,glob O,glob HybOrcl,Count.c,res}).
  + proc. inline A'(Orcl2(O), HybOrcl(Orcl2(O), OrclCount(L(Orcl2(O))))).main; wp.
    call (: ={glob O, Count.c, glob HybOrcl}).
    + by proc (={glob Count, glob HybOrcl}).
    + proc *.
      inline A'(Orcl2(O), HybOrcl(Orcl2(O), OrclCount(L(Orcl2(O))))).O.orcl Orcl2(O).orclL; wp.
      by call (: true); wp.
    + proc.
      inline HybOrcl(Orcl2(O), OrclCount(L(Orcl2(O)))).orcl.
      inline OrclCount(L(Orcl2(O))).orcl L(Orcl2(O)).orcl Orcl2(O).orclR.
      sp; if=> //.
      + by wp; call (: true); auto.
      if=> //.
      + inline OrclL(O).orcl Count.incr.
        by wp; call (: true); auto.
      by wp; call (: true); auto.
  by wp;rnd;auto; smt(q_pos).

  by inline *; auto.
have ->:   Pr[INDR(O, HybGame2(A)).main() @ &m:
                res /\ p (glob A) (glob O) HybOrcl.l /\ HybOrcl.l <= q /\ Count.c <= 1]
         = Pr[Rn(Orcl2(O), H.HybGame(A')).main() @ &m :
                ((res /\ p (glob A) (glob O) HybOrcl.l) /\ HybOrcl.l <= q) /\ Count.c <= 1].
+ byequiv (: ={glob A,glob O}
             ==> ={res,glob A,glob O,glob HybOrcl, Count.c})=> //.
  proc.
  call (: ={glob A,glob O, Count.c} ==> ={glob A,glob O,glob HybOrcl,Count.c,res}).
  + proc; inline A'(Orcl2(O), HybOrcl(Orcl2(O), OrclCount(R(Orcl2(O))))).main; wp.
    call (: ={glob O, Count.c, glob HybOrcl}).
    + by proc (={glob Count, glob HybOrcl}).
    + proc *.
      inline A'(Orcl2(O), HybOrcl(Orcl2(O), OrclCount(R(Orcl2(O))))).O.orcl Orcl2(O).orclL;wp.
      by call (: true); wp.
    + proc.
      inline HybOrcl(Orcl2(O), OrclCount(R(Orcl2(O)))).orcl.
      inline OrclCount(R(Orcl2(O))).orcl L(Orcl2(O)).orcl Orcl2(O).orclR.
      sp; if=> //.
      + by wp; call (: true); auto.
      if=> //.
      + inline OrclR(O).orcl Count.incr.
        by wp; call (: true); auto.
      by wp; call (: true); auto.
  by wp;rnd;auto; smt(q_pos).
  by inline *; auto.
have ->:   Pr[INDL(O, A).main() @ &m : res /\ p (glob A) (glob O) Count.c /\ Count.c <= q]
         = Pr[Ln(Orcl2(O), A').main() @ &m : (res /\ p (glob A) (glob O) Count.c) /\ Count.c <= q].
+ byequiv (: ={glob A,glob O}
             ==> ={res,glob A,glob O, Count.c})=> //.
  proc.
  call (: ={glob A,glob O, Count.c} ==> ={glob A,glob O,Count.c,res}).
  + proc *; inline A'(Orcl2(O), OrclCount(L(Orcl2(O)))).main; wp.
    call (: ={glob O, Count.c})=> //.
    + by proc *; wp; call (: true); wp.
    + proc *; inline A'(Orcl2(O), OrclCount(L(Orcl2(O)))).O.orcl Orcl2(O).orclL; wp.
      by call (: true); wp.
    proc; inline OrclCount(L(Orcl2(O))).orcl L(Orcl2(O)).orcl Orcl2(O).orclL Count.incr.
    by wp; call (: true); wp.
  by inline *; auto.
have ->:   Pr[INDR(O, A).main() @ &m : res /\ p (glob A) (glob O) Count.c /\ Count.c <= q]
         = Pr[Rn(Orcl2(O), A').main() @ &m : (res /\ p (glob A) (glob O) Count.c) /\ Count.c <= q].
+ byequiv (: ={glob A,glob O}
             ==> ={res,glob A,glob O, Count.c})=> //.
  proc.
  call (: ={glob A,glob O, Count.c} ==> ={glob A,glob O,Count.c,res}).
  + proc *; inline A'(Orcl2(O), OrclCount(R(Orcl2(O)))).main; wp.
    call (: ={glob O, Count.c})=> //.
    + by proc *; wp; call (: true); wp.
    + proc *; inline A'(Orcl2(O), OrclCount(R(Orcl2(O)))).O.orcl Orcl2(O).orclL; wp.
      by call (: true); wp.
    proc; inline OrclCount(R(Orcl2(O))).orcl R(Orcl2(O)).orcl Orcl2(O).orclR Count.incr.
    by wp; call(: true); wp.
  by inline *; auto.
apply: (Hybrid_div (Orcl2(O)) A' losslessL _ _ _ &m (fun ga go c b, b /\ p ga go c)).
+ by proc; call losslessO.
+ by proc; call losslessO.
move=> Ob LR Hlr Hl Ho1 Ho2; proc.
call (losslessA (<: A'(Ob,LR).O) (<: A'(Ob,LR).LR') _ _ _)=> //.
+ by proc; call Hlr.
+ by proc; call Ho1.
+ smt(q_pos).
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

module INDb(O:Orcl) (A:Adv) = {
  proc main():bool = {
    var b' : bool;

    Count.init();
    Orclb.b <$ {0,1};
    b' <@ A(O,Orclb(O)).main();
    return Orclb.b = b';
  }
}.

section.
declare module O <: Orcl {-Count, -Orclb}.
declare module A <: Adv  {-Count, -O, -Orclb}.

local module WA = {
  proc work(x : bool) : bool = {
    var b' : bool;

    Count.init();
    Orclb.b <- x;
    b' <@ A(O,Orclb(O)).main();
    return b';
  }
}.

lemma INDb_INDLR &m (p:glob A -> glob O -> int -> bool):
      Pr[INDb(O,A).main() @ &m : res /\ p (glob A) (glob O) Count.c]
    - Pr[INDR(O,A).main() @ &m : p (glob A) (glob O) Count.c]/2%r
  = (  Pr[INDL(O,A).main() @ &m : res /\ p (glob A) (glob O) Count.c]
     - Pr[INDR(O,A).main() @ &m : res /\ p (glob A) (glob O) Count.c]) / 2%r.
proof.
have //= H:= Sample_bool WA &m (fun (g:glob WA), let (ga,go,b,c) = g in p ga go c).
have ->:   Pr[INDb(O, A).main() @ &m : res /\ p (glob A) (glob O) Count.c]
         = Pr[MB.M.Rand(WA).main() @ &m : fst res = snd res /\ p (glob A) (glob O) Count.c].
+ byequiv (: ={glob A,glob O}
             ==>    ={glob A,glob O, Count.c}
                 /\ res{1} = (fst res = snd res){2})=> //.
  proc.
  inline Count.init WA.work=> //=.
  by swap{1} 2 -1; sim; proc (={Orclb.b, Count.c}).
have He: equiv [INDR(O, A).main ~ WA.work:
                     x{2} = false
                  /\ ={glob A,glob O}
                  ==> ={res,glob A,glob O, Count.c}].
+ proc.
  call (: ={glob O, Count.c} /\ Orclb.b{2} = false).
  + by proc (={Count.c} /\ Orclb.b{2} = false).
  + by proc (={Count.c} /\ Orclb.b{2} = false).
  + by proc; inline Count.incr; wp; call (: true); auto.
  by inline Count.init; auto.
have ->:   Pr[INDR(O, A).main() @ &m : p (glob A) (glob O) Count.c]
         = Pr[WA.work(false) @ &m : p (glob A) (glob O) Count.c].
+ by byequiv He.
have ->:   Pr[INDR(O, A).main() @ &m : res /\ p (glob A) (glob O) Count.c]
         = Pr[WA.work(false) @ &m : res /\ p (glob A) (glob O) Count.c].
+ by byequiv He.
have -> //:   Pr[INDL(O, A).main() @ &m : res /\ p (glob A) (glob O) Count.c]
            = Pr[WA.work(true) @ &m : res /\ p (glob A) (glob O) Count.c].
byequiv (: x{2} = true /\ ={glob A,glob O} ==> ={res,glob A,glob O, Count.c})=> //.
proc; call (: ={glob O, Count.c} /\ Orclb.b{2} = true).
+ by proc (={Count.c} /\ Orclb.b{2} = true).
+ by proc (={Count.c} /\ Orclb.b{2} = true).
+ by proc; inline Count.incr; wp; call (: true); auto.
by inline Count.init; auto.
qed.
end section.
