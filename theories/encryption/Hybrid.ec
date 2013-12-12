require import Int.
require import Real.
require import FSet.
require import ISet.
require import Pair.
require import Distr.
require import Monoid.
require Means.

type input.
type output.
type inleaks.
type outleaks.
type outputA.

module C = { 
  var c : int
  proc init () : unit = {
    c = 0;
  }
  proc incr () : unit = {
    c = c + 1;
  }
}.

module type Orcl = { 
  proc orcl(m:input) : output
}.

module Orclc(O:Orcl) = {
  proc orcl(m:input) : output = {
    var r : output;
    r = O.orcl(m);
    C.incr();
    return r;
  }
}.
module type Adversary = {
  proc main():outputA
}.

module Ac (A:Adversary) = {
  proc main():outputA = {
    var r:outputA;
    C.init();
    r = A.main();
    return r;
  }
}.

module type OrclAdv (O:Orcl) = {
  proc main () : outputA 
}.

module type Orclb = {
  proc leaks (il:inleaks) : outleaks  
  proc orcl1 (m:input) : output
  proc orcl2 (m:input) : output
}.

(* I would like to to 
module L(Ob:Orclb) : Orcl = {
  proc orcl = Ob.orcl1 (*No need to inline, direct application *)
}.
or 
module L(Ob:Orclb) : Orcl = {
  proc orcl(z:xxx) = Ob.orcl1(z) 
           (* Allow to rename the argument but need to inline *)
}
Remark it could be good to refers to a function parameter in spec by it relative
position (i.e no need to respect the name)
at least internally.
Then the printing will be in charge to use the good name.
*)

module L (Ob:Orclb) : Orcl = {
  proc orcl (m:input) : output = {
    var r : output;
    r = Ob.orcl1(m);
    return r;
  }
}.

module R (Ob:Orclb) : Orcl = {
  proc orcl (m:input) : output = {
    var r : output;
    r = Ob.orcl2(m);
    return r;
  }
}.

module LoR (Ob:Orclb) : Orcl = {
  var b:bool
  proc orcl (m:input) : output = {
    var r : output;
    if (b) r = Ob.orcl1(m);
    else r = Ob.orcl2(m);
    return r;
  }
}.

module type OrclbAdv (Ob:Orclb, O:Orcl) = {
  proc main () : outputA
}.

module Orcln (A:OrclAdv, O:Orcl) = Ac(A(Orclc(O))). 

module Ln(Ob:Orclb,A:OrclbAdv) = Orcln(A(Ob), L(Ob)).
  
module Rn(Ob:Orclb,A:OrclbAdv) = Orcln(A(Ob), R(Ob)).

module LRB (Ob:Orclb,O:Orcl) = {
  var l, l0 : int  
  proc orcl(m:input):output = {
    var r : output;
    if (l0 < l) r = Ob.orcl1(m);
    else { 
      if (l0 = l) r = O.orcl(m);
      else r = Ob.orcl2(m);
    }
    l = l + 1;
    return r;
  }    
}.

op q : int.
  
module B(A:OrclbAdv, Ob:Orclb, O:Orcl) = {
  module LR = LRB(Ob,O)
  module A = A(Ob,LR)
  proc main():outputA = {
    var r:outputA;
    LRB.l0 = $[0..q-1];
    LRB.l  = 0;
    r = A.main();
    return r;
  }
}.

clone import Means as M with
  type input <- int,
  type output <- outputA,
  op d <- [0..q-1].

(* A proof that it is equivalent to considere n call to the oracle or 1 call *)
section.

  declare module Ob : Orclb    {C,LRB}.
  declare module A  : OrclbAdv {C,LRB,Ob}.

  local module W (O:Orcl) = {
    module LR = LRB(Ob,O)
    module A = A(Ob,LR)
    proc work(x:int) : outputA = {
      var r:outputA;
      LRB.l = 0; LRB.l0 = x;
      r = A.main();
      return r;
    }
  }.

  local equiv Obleaks : Ob.leaks ~ Ob.leaks : ={il,glob Ob} ==> ={res,glob Ob}.
  proof strict. by proc true. qed.

  local equiv Oborcl1 : Ob.orcl1 ~ Ob.orcl1 : ={m,glob Ob} ==> ={res,glob Ob}.
  proof strict. by proc true. qed.

  local equiv Oborcl2 : Ob.orcl2 ~ Ob.orcl2 : ={m,glob Ob} ==> ={res,glob Ob}.
  proof strict. by proc true. qed.

  local lemma GLB_WL &m (p:glob A -> glob Ob -> int -> outputA -> bool):
    Pr[Ln(Ob,B(A)).main() @ &m : p (glob A) (glob Ob) LRB.l res /\ C.c <= 1] = 
    Pr[Rand(W(L(Ob))).main() @ &m : p (glob A) (glob Ob) LRB.l (snd res)].
  proof strict.
    byequiv (_ : ={glob A, glob Ob} ==> 
                    ={glob A, glob Ob,glob LRB} /\ res{1} = snd res{2} /\ 
                     C.c{1} <= 1) => //;proc. 
    inline{1}B(A, Ob, Orclc(L(Ob))).main; inline{2}W(L(Ob)).work;wp.
    call (_: ={glob Ob, glob LRB} /\ C.c{1} = (LRB.l0{1} < LRB.l{1}) ? 1 : 0).
      proc;wp.
      if => //;first by call Oborcl1;skip;progress => //; smt.
      if => //.
        inline{1} Orclc(L(Ob)).orcl L(Ob).orcl C.incr;inline{2} L(Ob).orcl.
        by wp;call Oborcl1;wp;skip;progress => //;smt.
      by call Oborcl2;skip;progress => //; smt.
      by conseq * Obleaks.
      by conseq * Oborcl1.
      by conseq * Oborcl2.
    swap{1} 1 2;inline{1} C.init.
    by wp;rnd;wp;skip;progress => //;smt.
  qed.

  local lemma GRB_WR &m (p:glob A -> glob Ob -> int -> outputA -> bool):
    Pr[Rn(Ob,B(A)).main() @ &m : p (glob A) (glob Ob) LRB.l res /\ C.c <= 1] = 
    Pr[Rand(W(R(Ob))).main() @ &m : p (glob A) (glob Ob) LRB.l (snd res)].
  proof strict.
    byequiv (_ : ={glob A, glob Ob} ==> 
                    ={glob A, glob Ob, glob LRB} /\ res{1} = snd res{2} /\ 
                    C.c{1} <= 1) => //;proc.
    inline{1}B(A, Ob, Orclc(R(Ob))).main; inline{2}W(R(Ob)).work;wp.
    call (_: ={glob Ob, glob LRB} /\ C.c{1} = (LRB.l0{1} < LRB.l{1}) ? 1 : 0).
      proc;wp.
      if => //;first by call Oborcl1;skip;progress => //; smt.
      if => //.
        inline{1} Orclc(R(Ob)).orcl R(Ob).orcl C.incr;inline{2} R(Ob).orcl.
        by wp;call Oborcl2;wp;skip;progress => //;smt.
      by call Oborcl2;skip;progress => //; smt.
      by conseq * Obleaks.
      by conseq * Oborcl1.
      by conseq * Oborcl2.
    swap{1} 1 2;inline{1} C.init.
    by wp;rnd;wp;skip;progress => //;smt.
  qed.

  axiom losslessL: islossless Ob.leaks.
  axiom losslessOb1: islossless Ob.orcl1. 
  axiom losslessOb2: islossless Ob.orcl2. 
  axiom losslessA (Ob0 <: Orclb{A}) (LR <: Orcl{A}):
    islossless LR.orcl => 
    islossless Ob0.leaks => islossless Ob0.orcl1 => islossless Ob0.orcl2 =>
    islossless A(Ob0, LR).main.

  axiom q_pos : 0 < q.

  local lemma WL0_GLA &m (p:glob A -> glob Ob -> int -> outputA -> bool): 
     Pr[W(L(Ob)).work(0) @ &m : p (glob A) (glob Ob) LRB.l res /\ LRB.l <= q] = 
     Pr[Ln(Ob,A).main() @ &m : p (glob A) (glob Ob) C.c res /\ C.c <= q ].
  proof strict.
    byequiv (_ : ={glob A, glob Ob} /\ x{1}=0 ==> 
                    (LRB.l{1} <= q) = (C.c{2} <= q) /\
                    (C.c{2} <= q =>
                      ={glob A, glob Ob,res} /\ LRB.l{1} = C.c{2})) => //;
     [proc | smt].
    call (_: q < C.c,
             ={glob Ob} /\ LRB.l0{1} = 0 /\ LRB.l{1} = C.c{2} /\ 0 <= LRB.l{1},
             LRB.l0{1} = 0 /\ q < LRB.l{1}).
      by apply losslessA.
      proc;inline{2} C.incr L(Ob).orcl;wp.
      if{1};first by call Oborcl1;wp;skip;progress => //;smt.
      rcondt{1} 1; first by intros &m0;skip;smt.
      by inline{1} L(Ob).orcl;wp;call Oborcl1;wp;skip;progress => //;smt.
      intros &m2 _;proc.
      rcondt 1; first by skip;smt.
      by wp;call losslessOb1;skip;smt.
      by intros &m1;proc;inline C.incr L(Ob).orcl;wp;call losslessOb1;wp;skip;smt.
      by conseq * Obleaks.
      intros &m2 _;conseq * losslessL.
      intros &m1; conseq * losslessL.

      by conseq * Oborcl1.
      intros &m2 _;conseq * losslessOb1.
      intros &m1; conseq * losslessOb1.

      by conseq * Oborcl2.
      intros &m2 _;conseq * losslessOb2.
      intros &m1; conseq * losslessOb2.

    by inline{2} C.init;wp;skip;smt.
  qed.

  local lemma WRq_GRA &m (p:glob A -> glob Ob -> int -> outputA -> bool): 
     Pr[W(R(Ob)).work((q-1)) @ &m :  p (glob A) (glob Ob) LRB.l res /\ LRB.l <= q] = 
     Pr[Rn(Ob,A).main() @ &m :  p (glob A) (glob Ob) C.c res /\ C.c <= q ].
  proof strict.
    byequiv (_ : ={glob A, glob Ob} /\ x{1}=q-1 ==> 
                    (LRB.l{1} <= q) = (C.c{2} <= q) /\
                    (C.c{2} <= q =>
                      ={glob A, glob Ob, res} /\ LRB.l{1} = C.c{2})) => //;
    [proc | smt].
    call (_: q < C.c,
             ={glob Ob} /\ LRB.l0{1} = q-1 /\ LRB.l{1} = C.c{2} /\ 0 <= LRB.l{1},
             LRB.l0{1} = q-1 /\ q < LRB.l{1}).
      by apply losslessA.

      proc;inline{2} C.incr R(Ob).orcl;wp.
      if{1};first by call{1} losslessOb1;call{2} losslessOb2;wp;skip; smt.
      inline{1} R(Ob).orcl;if{1};
        first by wp;call Oborcl2;wp;skip;progress => //;smt.
      by call Oborcl2;wp;skip;progress => //;smt.
      intros &m2 _;proc.
      rcondt 1; first by skip;smt.
      by wp;call losslessOb1;skip; smt.
      intros &m1;proc;inline C.incr R(Ob).orcl;wp;call losslessOb2;wp;skip;smt.

      by conseq * Obleaks.
      intros &m2 _;conseq * losslessL.
      intros &m1; conseq * losslessL.

      by conseq * Oborcl1.
      intros &m2 _;conseq * losslessOb1.
      intros &m1; conseq * losslessOb1.

      by conseq * Oborcl2.
      intros &m2 _;conseq * losslessOb2.
      intros &m1; conseq * losslessOb2.

    by inline{2} C.init;wp;skip;smt.
  qed.

  local lemma WLR_shift &m v (p:glob A -> glob Ob -> int -> outputA -> bool): 
    1 <= v <= q-1 => 
    Pr[W(L(Ob)).work(v) @ &m: p (glob A) (glob Ob) LRB.l res] = 
    Pr[W(R(Ob)).work((v-1)) @ &m : p (glob A) (glob Ob) LRB.l res].
  proof strict.
    intros Hv;byequiv (_: ={glob A,glob Ob} /\ x{1} = v /\ x{2} = v-1 ==> 
                             ={glob A,glob Ob, LRB.l, res}) => //.
    proc.
    call (_: ={glob Ob, LRB.l} /\ LRB.l0{1} = v /\ LRB.l0{2} = v-1).
      proc.
      if{1}; first by rcondt{2} 1;[intros &m0;skip;smt | wp;call Oborcl1].
      if{1};first by rcondt{2} 1;
       [intros &m0;skip;smt | inline{1} L(Ob).orcl;wp;call Oborcl1;wp].
      rcondf{2} 1;first by intros &m0;skip;smt.
      by inline{2} R(Ob).orcl;if{2};wp;call Oborcl2;wp.
      by conseq * Obleaks.
      by conseq * Oborcl1.
      by conseq * Oborcl2.
    by wp.
  qed.

  (* TODO : move this *)
  lemma Mrplus_inter_shift (i j k:int) f: 
      Mrplus.sum f (Interval.interval i j) = 
      Mrplus.sum (fun l, f (l + k)) (Interval.interval (i-k) (j-k)).
  proof strict.
    rewrite (Mrplus.sum_chind f (fun l, l - k) (fun l, l + k)) /=;first smt.
    congr => //.   
    apply FSet.set_ext => x.
    rewrite img_def Interval.mem_interval;split.
      intros [y];rewrite Interval.mem_interval;smt.
    intros Hx;exists (x+k);rewrite Interval.mem_interval;smt.
  qed.

  lemma Hybrid &m (p:glob A -> glob Ob -> int -> outputA -> bool):
     let p' = fun ga ge l r, p ga ge l r /\ l <= q in
     Pr[Ln(Ob,B(A)).main() @ &m : p' (glob A) (glob Ob) LRB.l res /\ C.c <= 1] - 
       Pr[Rn(Ob,B(A)).main() @ &m : p' (glob A) (glob Ob) LRB.l res /\ C.c <= 1] =
     1%r/q%r * (
       Pr[Ln(Ob,A).main() @ &m : p' (glob A) (glob Ob) C.c res] - 
         Pr[Rn(Ob,A).main() @ &m : p' (glob A) (glob Ob) C.c res]).
  proof strict.
    intros p';rewrite (GLB_WL &m p') (GRB_WR &m p').
    simplify p'; rewrite -(WL0_GLA &m p) -(WRq_GRA &m p).
    cut Hint : Finite.(==) (create (support [0..q - 1])) (Interval.interval 0 (q - 1)).
      by intros x;rewrite mem_create Interval.mem_interval /support Dinter.supp_def.
    cut Hfin: Finite.finite (create (support [0..q - 1])).
      by exists (Interval.interval 0 (q-1)).
    cut Huni : forall (x : int), in_supp x [0..q - 1] => mu_x [0..q - 1] x = 1%r / q%r.
      by intros x Hx;rewrite Dinter.mu_x_def_in //;smt.
    pose ev := 
      fun (_j:int) (g:glob W(L(Ob))) (r:outputA),
        let (l,l0,ge,ga) = g in p ga ge l r /\ l <= q.
    cut := M.Mean_uni (W(L(Ob))) &m ev (1%r/q%r) _ _ => //; simplify ev => ->.
    cut := M.Mean_uni (W(R(Ob))) &m ev (1%r/q%r) _ _ => //; simplify ev => ->.
    cut -> : Finite.toFSet (create (support [0..q - 1])) = Interval.interval 0 (q-1).
      apply FSet.set_ext => x.
      by rewrite Interval.mem_interval Finite.mem_toFSet // 
           mem_create /support Dinter.supp_def.
    (* BUG type are not normalized in ev => assert failure in ecWhy *)      
    clear ev.
    rewrite {1}Interval.interval_addl; first by smt.
    rewrite (Interval.interval_pos 0 (q-1));first by smt.
    rewrite Mrplus.sum_add /=.
      by rewrite Interval.mem_interval.
    rewrite Mrplus.sum_add /=.
      by rewrite Interval.mem_interval;smt.
    cut Hq : q%r <> Real.zero by smt.
    fieldeq => //.
    rewrite -(Mrplus.sum_comp (( * ) (-1)%r)) //;first intros x y;ringeq.
    rewrite (Mrplus_inter_shift 0 (q - 1 - 1) (-1)) /=.
    cut -> : q - 1 - 1 - -1 = q - 1; first by smt.
    rewrite Mrplus.sum_add2.
    rewrite (Mrplus.NatMul.sum_const 0%r) /Mrplus.NatMul.( * ) /=;last ringeq.
    intros x; rewrite Interval.mem_interval => Hx.
    cut := WLR_shift &m x p' _ => //;simplify p' => ->.
      (* cut -> : x + -1 = x - 1     BUG *) 
    by smt.
  qed.

end section.
