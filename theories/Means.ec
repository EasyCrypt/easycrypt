(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

require import Int.
require import FSet.
require import Real.
require import Distr.

require import Monoid.
require import ISet.
require import Pair.

theory Mean.
  type input.
  type output.

  op d : input distr.
  
  module type Worker = {
    proc work(x:input) : output
  }.

  module Rand (W:Worker) = {
    proc randAndWork() : input * output = {
      var x : input;
      var r : output;

      x = $d;
      r = W.work(x);
      return (x,r);
    }
  }.

  lemma prCond (A <: Worker) &m (v:input)
               (ev:input -> glob A -> output -> bool):
      Pr[Rand(A).randAndWork() @ &m: ev v (glob A) (snd res) /\ v = fst res] =
        (mu_x d v) * Pr[A.work(v) @ &m : ev v (glob A) res].
  proof strict.
  byphoare (_: (glob A) = (glob A){m} ==> 
                   ev (fst res) (glob A) (snd res) /\ fst res = v) => //.
  pose pr := Pr[A.work(v) @ &m: ev v (glob A) res];
  conseq* (_: _: = (mu_x d v * pr)). (* WEIRD! *)
  proc; seq 1 : (v = x) (mu_x d v) pr 1%r 0%r ((glob A)=(glob A){m})=> //.
    by rnd.
    by rnd; skip; progress=> //; rewrite /mu_x; apply mu_eq.
    call (_: (glob A) = (glob A){m} /\ x = v ==> 
             ev v (glob A) res) => //.
    simplify pr; bypr => &m' eqGlob.
    by byequiv (_: ={glob A, x} ==> ={res, glob A}) => //; proc true. 
    by conseq* (_: _ ==> false)=> //.
  qed.

  lemma introOrs (A <: Worker) &m (ev:input -> glob A -> output -> bool):
    Finite.finite (create (support d)) =>
    let sup = Finite.toFSet (create (support d)) in
    Pr[Rand(A).randAndWork() @ &m: ev (fst res) (glob A) (snd res)] =
     Pr[Rand(A).randAndWork() @ &m:
          cpOrs (img (fun v r, ev v (glob A) (snd r) /\ v = fst r) sup) res].
  proof strict.
  intros=> Fsup sup.
  byequiv (_: ={glob A} ==> ={glob A, res} /\ in_supp (fst res{1}) d)=> //;
    first by proc; call (_: true); rnd.
  intros=> &m1 &m2 [[<- <-] Hin].
  rewrite /cpOrs or_exists;split.
    intros=> H.
    exists (fun r, 
              ev (fst res{m1}) (glob A){m1} (snd r) /\ (fst res{m1}) = fst r).
    split=> //. 
    by rewrite img_def; exists (fst (res{m1})); smt.
    by intros=> [x]; rewrite img_def => /= [[v [<- /= Hm] [H1 <- ]]].
  qed.

  lemma Mean (A <: Worker) &m (ev:input -> glob A -> output -> bool): 
    Finite.finite (create (support d)) =>
    let sup = Finite.toFSet (create (support d)) in
    Pr[Rand(A).randAndWork()@ &m: ev (fst res) (glob A) (snd res)] =
     Mrplus.sum
       (fun (v:input), mu_x d v * Pr[A.work(v)@ &m:ev v (glob A) res]) 
       sup.
  proof strict.
  intros=> Fsup /=.
  cut:= introOrs A &m ev _=> //= ->.
  elim/set_ind (Finite.toFSet (create (support d))).
    rewrite Mrplus.sum_empty.
    byphoare (_ : true ==> false)=> //.
    by rewrite /cpOrs img_empty Mbor.sum_empty.
    intros=> x s Hx Hrec.
    rewrite Mrplus.sum_add //=.
    cut ->: Pr[Rand(A).randAndWork() @ &m:
                 cpOrs (img (fun (v : input) (r : input * output),
                               ev v (glob A) (snd r) /\ v = fst r) (add x s)) res] =
             Pr[Rand(A).randAndWork() @ &m:
                 (ev x (glob A) (snd res) /\ x = fst res) \/
                 cpOrs (img (fun (v : input) (r : input * output),
                               ev v (glob A){hr} (snd r) /\ v = fst r) s) res].
      rewrite Pr[mu_eq] => // &m1.
      pose f:= (fun (v : input) (r : input * output),
                  ev v (glob A){m1} (snd r) /\ v = fst r).
      by rewrite img_add cpOrs_add; smt.
    rewrite Pr[mu_disjoint]; first by smt.
    by rewrite Hrec (prCond A &m x ev).
  qed.

  lemma Mean_uni (A<:Worker) &m (ev:input -> glob A -> output -> bool) r: 
     (forall x, in_supp x d => mu_x d x = r) =>
     Finite.finite (create (support d)) =>
     let sup = Finite.toFSet (create (support d)) in
     Pr[Rand(A).randAndWork()@ &m: ev (fst res) (glob A) (snd res)] =
       r * Mrplus.sum (fun (v:input), Pr[A.work(v)@ &m:ev v (glob A) res]) sup.
  proof -strict.
    intros Hd Hfin /=.
    cut := Mean A &m ev => /= -> //.
    cut := Mrplus.sum_comp (( * ) r) (fun (v:input), Pr[A.work(v)@ &m:ev v (glob A) res]) => /= <-.
      by intros x y; smt.
    apply Mrplus.sum_eq => /= x.
    by rewrite Finite.mem_toFSet // mem_create /support => Hin;rewrite Hd.
  qed.
   
end Mean.

theory LR.

  clone import Mean as M with
    type input <- bool,
    type output <- bool,
    op d <- {0,1}.

  lemma Sample_LR (A<:Worker) &m:
    Pr[A.work(false) @ &m : true] = 1%r =>
    Pr[Rand(A).randAndWork() @ &m : fst res = snd res] - 1%r/2%r = 
      1%r/2%r*(Pr[A.work(true) @ &m : res] - Pr[A.work(false) @ &m : res]).
  proof strict.
    intros Hloss.
    pose ev := fun (b:bool) (gA:glob A) (b':bool), b = b'.
    cut -> : Pr[Rand(A).randAndWork() @ &m : fst res = snd res] =
             Pr[Rand(A).randAndWork() @ &m : ev (fst res) (glob A) (snd res)] by trivial.
    cut Hcr: forall x, 
               mem x (create (support {0,1})) <=>
               mem x (add true (add false (FSet.empty)%FSet)).
      by intros=> x; rewrite !FSet.mem_add; case x=> //=; smt.
    cut Hf : Finite.finite (create (support {0,1})).
      by exists (FSet.add true (FSet.add false FSet.empty)) => x;apply Hcr.
    cut := Mean A &m ev => /= -> //.
    cut -> : 
      Finite.toFSet (create (support {0,1})) = (FSet.add true (FSet.add false FSet.empty)).
      by apply FSet.set_ext => x; rewrite Finite.mem_toFSet //;apply Hcr.
    rewrite Mrplus.sum_add;first smt.
    rewrite Mrplus.sum_add;first smt.
    rewrite Mrplus.sum_empty /= !Bool.Dbool.mu_x_def;simplify ev.
    cut Hd: 2%r <> Real.zero by smt.
    cut -> : Pr[A.work(true) @ &m : true = res] = Pr[A.work(true) @ &m : res].
      by rewrite Pr[mu_eq];smt.
    cut -> : Pr[A.work(false) @ &m : false = res] = Pr[A.work(false) @ &m : !res].
      by rewrite Pr[mu_eq];smt.       
    rewrite Pr[mu_not].
    by rewrite Hloss; smt.
  qed.

end LR.

theory Hybrid.
  type input.
  type output.
  type leaks.
  op in0 : input.
  type outputA.

  module type Enc = { 
    proc init () : unit 
    proc leaks () : leaks  
    proc enc (m:input) : output
  }.

  module type AEnc = {
    proc enc (m:input) : output
  }.

  module type EAdv(E:Enc, AE: AEnc) = {
    proc run () : outputA
  }.

  module C = { 
    var c : int
    proc init () : unit = {
      c = 0;
    }
    proc incr () : unit = {
      c = c + 1;
    }
  }.

  module GE (A:EAdv, E:Enc) = {
    module Em = {
      proc enc(m:input) : output = {
        var r : output;
        r = E.enc(m);
        C.incr();
        return r;
      }
    }
      
    module A = A(E,Em)

    proc main () : outputA = {
      var r : outputA;
      C.init();
      r = A.run();
      return r;
    }
  }.

  module GE0(A:EAdv, E:Enc) = {
    module E0 = {
      proc enc(m:input) : output = {
        var r : output;
        r = E.enc(in0);
        C.incr();
        return r;
      }
    }
    module A = A(E,E0)

    proc main () : outputA = {
      var r : outputA;
      C.init();
      r = A.run();
      return r;
    }
  }.

  module type LR = { 
    proc lr(m0 m1:input) : output
  }.
   
  module L(E:Enc) = {
    proc lr(m0 m1:input) : output = {
      var r : output;
      r = E.enc(m0);
      return r;
    }
  }.

  module R(E:Enc) = {
    proc lr(m0 m1:input) : output = {
      var r : output;
      r = E.enc(m1);
      return r;
    }
  }. 

  module type LRAdv(E:Enc, LR:LR) = {
    proc run () : outputA
  }.

  module GL(A:LRAdv, E:Enc) = {
    module L = { 
      proc lr(m0 m1:input) : output = {
        var r : output;
        r = E.enc(m0);
        C.incr();
        return r;
      }
    }

    module A = A(E,L)

    proc main () : outputA = {
      var r : outputA;
      C.init();
      r = A.run();
      return r;
    }
  }.

  module GR(A:LRAdv, E:Enc) = {
    module R = {
      proc lr(m0 m1:input) : output = {
        var r : output;
        r = E.enc(m1);
        C.incr();
        return r;
      }
    }

    module A = A(E,R)

    proc main () : outputA = {
      var r : outputA;
      C.init();
      r = A.run();
      return r;
    }
  }.

  module BLR(A:EAdv, E:Enc, LR:LR) = {
    module Elr = {
      proc enc(m:input) : output = {
        var r : output;
        r = LR.lr(m, in0);
        return r;
      }
    }
    module A = A(E,Elr)
    proc run () : outputA = {
      var r : outputA;
      r = A.run();
      return r;
    }
  }.

  equiv Cinit : C.init ~ C.init : true ==> ={C.c}.
  proof strict. by proc;wp. qed.

  equiv Cincr : C.incr ~ C.incr : ={C.c} ==> ={C.c}.
  proof strict. by proc;wp. qed.
 
  section. (* E0_LR. *)
    declare module E : Enc{C}.
    declare module A : EAdv{E,C}.

    equiv GE_GL : GE(A,E).main ~ GL(BLR(A),E).main : 
                    ={glob A,glob E} ==> ={res,glob A,glob E,C.c}.
    proof strict.
      proc;inline{2} GL(BLR(A), E).A.run;wp.
      call (_: ={glob E, C.c}).
        proc;inline{2} GL(BLR(A), E).L.lr;wp.
        by call Cincr; call(_: true);wp.
        by proc (={C.c}).
        by proc (={C.c}).
        by proc (={C.c}).
      by call Cinit.
    qed.

    equiv GE0_GR : GE0(A,E).main ~ GR(BLR(A),E).main : 
                     ={glob A,glob E} ==> ={res,glob A,glob E,C.c}.
    proof strict.
      proc;inline{2} GR(BLR(A), E).A.run;wp.
      call (_: ={glob E,C.c}).
        proc;inline{2} GR(BLR(A), E).R.lr;wp.
        by call Cincr; call(_: true);wp.
        by proc (={C.c}).
        by proc (={C.c}).
        by proc (={C.c}).
      by call Cinit.
    qed.

    lemma E0_LR &m (p:glob A -> glob E -> int -> outputA -> bool): 
      Pr[GE(A,E).main() @ &m : p (glob A) (glob E) C.c res] - 
      Pr[GE0(A,E).main() @ &m : p (glob A) (glob E) C.c res] =
      Pr[GL(BLR(A),E).main() @ &m : p (glob A) (glob E) C.c res] -
      Pr[GR(BLR(A),E).main() @ &m : p (glob A) (glob E) C.c res].
    proof -strict.
      congr;last by byequiv GE0_GR.
      by byequiv GE_GL.
    qed.

  end section.

  module LRB (E:AEnc,LR:LR) = {
    var l, l0 : int  
    proc lr(m0 m1:input):output = {
      var r : output;
      if (l0 < l) r = E.enc(m0);
      else { 
        if (l0 = l) r = LR.lr(m0,m1);
        else r = E.enc(m1);
      }
      l = l + 1;
      return r;
    }    
  }.

  op q : int.
  
  module B(A:LRAdv, E:Enc, LR0:LR) = {
    module LR = LRB(E,LR0)
    module A = A(E,LR)
    proc run():outputA = {
      var r:outputA;
      LRB.l0 = $[0..q-1];
      LRB.l  = 0;
      r = A.run();
      return r;
    }
  }.

  clone import Mean as M with
    type input <- int,
    type output <- outputA,
    op d <- [0..q-1].

  section.

    declare module E    : Enc   {C,LRB}.
    declare module A    : LRAdv   {C,LRB,E}.

    local module W (LR0:LR) = {
      module LR = LRB(E,LR0)
      module A = A(E,LR)
      proc work(x:int) : outputA = {
        var r:outputA;
        LRB.l = 0; LRB.l0 = x;
        r = A.run();
        return r;
      }
    }.

    local equiv Einit : E.init ~ E.init : ={glob E} ==> ={glob E}.
    proof strict. by proc true. qed.

    local equiv Eleaks : E.leaks ~ E.leaks : ={glob E} ==> ={res,glob E}.
    proof strict. by proc true. qed.

    local equiv Eenc : E.enc ~ E.enc : ={m,glob E} ==> ={res,glob E}.
    proof strict. by proc true. qed.

    local lemma GLB_WL &m (p:glob A -> glob E -> int -> outputA -> bool):
      Pr[GL(B(A),E).main() @ &m : p (glob A) (glob E) LRB.l res /\ C.c <= 1] = 
      Pr[Rand(W(L(E))).randAndWork() @ &m : p (glob A) (glob E) LRB.l (snd res)].
    proof strict.
      byequiv (_ : ={glob A, glob E} ==> 
                      ={glob A, glob E,glob LRB} /\ res{1} = snd res{2} /\ C.c{1} <= 1) => //.
      proc; inline{1} GL(B(A), E).A.run;inline{2} W(L(E)).work;wp.
      call (_: ={glob E, glob LRB} /\ C.c{1} = (LRB.l0{1} < LRB.l{1}) ? 1 : 0).
        proc;wp.
        if => //;first by call Eenc;skip;progress => //; smt.
        if => //.
          inline{1} GL(B(A), E).L.lr C.incr;inline{2} L(E).lr.
          by wp;call Eenc;wp;skip;progress => //;smt.
        by call Eenc;skip;progress => //; smt.
        by conseq * Einit; progress => //;smt.
        by conseq * Eleaks.
        by conseq * Eenc.
      swap{1} 1 2;inline{1} C.init.
      by wp;rnd;wp;skip;progress => //;smt.
    qed.

    local lemma GRB_WR &m (p:glob A -> glob E -> int -> outputA -> bool):
      Pr[GR(B(A),E).main() @ &m : p (glob A) (glob E) LRB.l res /\ C.c <= 1] = 
      Pr[Rand(W(R(E))).randAndWork() @ &m : p (glob A) (glob E) LRB.l (snd res)].
    proof strict.
      byequiv (_ : ={glob A, glob E} ==> 
                      ={glob A, glob E, glob LRB} /\ res{1} = snd res{2} /\ C.c{1} <= 1) => //.
      proc; inline{1} GR(B(A), E).A.run;inline{2} W(R(E)).work;wp.
      call (_: ={glob E, glob LRB} /\ C.c{1} = (LRB.l0{1} < LRB.l{1}) ? 1 : 0).
        proc;wp.
        if => //;first by wp;call Eenc;skip;progress => //; smt.
        if => //.
          inline{1} GR(B(A), E).R.lr C.incr;inline{2} R(E).lr.
          by wp;call Eenc;wp;skip;progress => //;smt.
        by call Eenc;skip;progress => //; smt.
        by conseq * Einit; progress => //;smt.
        by conseq * Eleaks.
        by conseq * Eenc.
      swap{1} 1 2;inline{1} C.init.
      by wp;rnd;wp;skip;progress => //;smt.
    qed.

    axiom losslessI: islossless E.init.
    axiom losslessL: islossless E.leaks.
    axiom losslessE: islossless E.enc. 
    axiom losslessA (E0 <: Enc{A}) (LR <: LR{A}):
      islossless LR.lr => islossless E0.init => islossless E0.leaks => islossless E0.enc => 
      islossless A(E0, LR).run.

    axiom q_pos : 0 < q.

    local lemma WL0_GLA &m (p:glob A -> glob E -> int -> outputA -> bool): 
       Pr[W(L(E)).work(0) @ &m : p (glob A) (glob E) LRB.l res /\ LRB.l <= q] = 
       Pr[GL(A,E).main() @ &m : p (glob A) (glob E) C.c res /\ C.c <= q ].
    proof strict.
      byequiv (_ : ={glob A, glob E} /\ x{1}=0 ==> 
                      (LRB.l{1} <= q) = (C.c{2} <= q) /\
                      (C.c{2} <= q =>
                        ={glob A, glob E,res} /\ LRB.l{1} = C.c{2})) => //;last smt.
      proc.
      call (_: q < C.c,
               ={glob E} /\ LRB.l0{1} = 0 /\ LRB.l{1} = C.c{2} /\ 0 <= LRB.l{1},
               LRB.l0{1} = 0 /\ q < LRB.l{1}).
        by apply losslessA.

        proc;inline{2} C.incr;wp.
        if{1};first by call Eenc;skip;progress => //;smt.
        rcondt{1} 1; first by intros &m0;skip;smt.
        by inline{1} L(E).lr;wp;call Eenc;wp;skip;progress => //;smt.
        intros &m2 _;proc.
        rcondt 1; first by skip;smt.
        by wp;call losslessE;skip;smt.
        by intros &m1;proc;inline C.incr;wp;call losslessE;wp;skip;smt.

        by conseq * Einit; progress => //;smt.
        intros &m2 _;conseq * losslessI.
        intros &m1; conseq * losslessI.

        by conseq * Eleaks.
        intros &m2 _;conseq * losslessL.
        intros &m1; conseq * losslessL.

        by conseq * Eenc.
        intros &m2 _;conseq * losslessE.
        intros &m1; conseq * losslessE.

      by inline{2} C.init;wp;skip;smt.
    qed.

    local lemma WRq_GRA &m (p:glob A -> glob E -> int -> outputA -> bool): 
       Pr[W(R(E)).work((q-1)) @ &m :  p (glob A) (glob E) LRB.l res /\ LRB.l <= q] = 
       Pr[GR(A,E).main() @ &m :  p (glob A) (glob E) C.c res /\ C.c <= q ].
    proof strict.
      byequiv (_ : ={glob A, glob E} /\ x{1}=q-1 ==> 
                      (LRB.l{1} <= q) = (C.c{2} <= q) /\
                      (C.c{2} <= q =>
                        ={glob A, glob E, res} /\ LRB.l{1} = C.c{2})) => //;last smt.
      proc.
      call (_: q < C.c,
               ={glob E} /\ LRB.l0{1} = q-1 /\ LRB.l{1} = C.c{2} /\ 0 <= LRB.l{1},
               LRB.l0{1} = q-1 /\ q < LRB.l{1}).
        by apply losslessA.

        proc;inline{2} C.incr;wp.
        if{1};first by call{1} losslessE;call{2} losslessE;skip; smt.
        inline{1} R(E).lr;if{1};first by wp;call Eenc;wp;skip;progress => //;smt.
        by call Eenc;skip;progress => //;smt.
        intros &m2 _;proc.
        rcondt 1; first by skip;smt.
        by wp;call losslessE;skip; smt.
        by intros &m1;proc;inline C.incr;wp;call losslessE;wp;skip;smt.

        by conseq * Einit; progress => //;smt.
        intros &m2 _;conseq * losslessI.
        intros &m1; conseq * losslessI.

        by conseq * Eleaks.
        intros &m2 _;conseq * losslessL.
        intros &m1; conseq * losslessL.

        by conseq * Eenc.
        intros &m2 _;conseq * losslessE.
        intros &m1; conseq * losslessE.

      by inline{2} C.init;wp;skip;smt.
    qed.

    local lemma WLR_shift &m v (p:glob A -> glob E -> int -> outputA -> bool): 1 <= v <= q-1 => 
         Pr[W(L(E)).work(v) @ &m: p (glob A) (glob E) LRB.l res] = 
         Pr[W(R(E)).work((v-1)) @ &m : p (glob A) (glob E) LRB.l res].
    proof strict.
      intros Hv;byequiv (_: ={glob A,glob E} /\ x{1} = v /\ x{2} = v-1 ==> 
                               ={glob A,glob E, LRB.l, res}) => //.
      proc.
      call (_: ={glob E, LRB.l} /\ LRB.l0{1} = v /\ LRB.l0{2} = v-1).
        proc.
        if{1}; first by rcondt{2} 1;[intros &m0;skip;smt | wp;call Eenc].
        if{1};first by rcondt{2} 1;[intros &m0;skip;smt | inline{1} L(E).lr;wp;call Eenc;wp].
        rcondf{2} 1;first by intros &m0;skip;smt.
        by inline{2} R(E).lr;if{2};wp;call Eenc;wp.
        by conseq * Einit; progress => //;smt.
        by conseq * Eleaks.
        by conseq * Eenc.
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

    lemma Hybrid &m (p:glob A -> glob E -> int -> outputA -> bool):
       let p' = fun ga ge l r, p ga ge l r /\ l <= q in
       Pr[GL(B(A),E).main() @ &m : p' (glob A) (glob E) LRB.l res /\ C.c <= 1] - 
         Pr[GR(B(A),E).main() @ &m : p' (glob A) (glob E) LRB.l res /\ C.c <= 1] = 
       1%r/q%r * (
         Pr[GL(A,E).main() @ &m : p' (glob A) (glob E) C.c res] - 
           Pr[GR(A,E).main() @ &m : p' (glob A) (glob E) C.c res]).
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
        fun (_j:int) (g:glob W(L(E))) (r:outputA),
          let (l,l0,ge,ga) = g in p ga ge l r /\ l <= q.
      cut := M.Mean_uni (W(L(E))) &m ev (1%r/q%r) _ _ => //; simplify ev => ->.
      cut := M.Mean_uni (W(R(E))) &m ev (1%r/q%r) _ _ => //; simplify ev => ->.
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

  module LRB0 (E:AEnc,AE:AEnc) = {
    proc enc(m:input):output = {
      var r : output;
      if (LRB.l0 < LRB.l) r = E.enc(m);
      else { 
        if (LRB.l0 = LRB.l) r = AE.enc(m);
        else r = E.enc(in0);
      }
      LRB.l = LRB.l + 1;
      return r;
    }    
  }.

  module B0(A:EAdv, E:Enc, AE:AEnc) = {
    module E0 = LRB0(E,AE)
    module A = A(E,E0)
    proc run():outputA = {
      var r:outputA;
      LRB.l0 = $[0..q-1];
      LRB.l  = 0;
      r = A.run();
      return r;
    }
  }.  

  lemma Hybrid0 (E <: Enc{C, LRB}) (A <: EAdv{C, LRB, E}) : 
    islossless E.init =>
    islossless E.leaks =>
    islossless E.enc =>
    (forall (E <: Enc{A}) (AE <: AEnc{A}),
       islossless AE.enc =>
       islossless E.init =>
       islossless E.leaks => islossless E.enc => islossless A(E, AE).run) =>
    0 < q =>
    forall &m (p : (glob A) -> (glob E) -> int -> outputA -> bool),
      let p' =
        fun (ga : (glob A)) (ge : (glob E)) (l : int) (r : outputA),
           p ga ge l r /\ l <= q in
      Pr[GE(B0(A), E).main() @ &m :
         p' (glob A){hr} (glob E){hr} LRB.l res /\ C.c <= 1] -
      Pr[GE0(B0(A), E).main() @ &m :
         p' (glob A){hr} (glob E){hr} LRB.l res /\ C.c <= 1] =
      1%r / q%r *
      (Pr[GE(A, E).main() @ &m : p' (glob A){hr} (glob E){hr} C.c res] -
       Pr[GE0(A, E).main() @ &m : p' (glob A){hr} (glob E){hr} C.c res]).
  proof strict. 
   intros Il Ll El Al Hq &m p p'.
   pose p2 := fun (g : (glob B0(A))) (ge : (glob E)) (c : int) (r : outputA),
               let (l,l0,ga) = g in p' ga ge l r /\ c <= 1.
   cut := E0_LR E (B0(A)) &m p2;simplify p2 => ->.
   rewrite (E0_LR E A &m p').
   cut -> : Pr[GL(BLR(B0(A)), E).main() @ &m :
              p' (glob A){hr} (glob E){hr} LRB.l res /\ C.c <= 1] = 
            Pr[GL(B(BLR(A)), E).main() @ &m :
              p' (glob A){hr} (glob E){hr} LRB.l res /\ C.c <= 1].
     byequiv (_: ={glob A, glob E} ==> ={glob A, glob E, LRB.l, C.c, res}) => //.
     proc.
     inline{1} GL(BLR(B0(A)), E).A.run BLR(B0(A), E, GL(BLR(B0(A)), E).L).A.run.
     inline{2} GL(B(BLR(A)), E).A.run B(BLR(A), E, GL(B(BLR(A)), E).L).A.run;wp.
     call (_: ={glob E, glob LRB, C.c}).
       proc;inline{2} LRB(E, GL(B(BLR(A)), E).L).lr;sim;sp.
       if => //;first by sim.
       if => //;last by call (_: true) => //;sim.
       inline{1} BLR(B0(A), E, GL(BLR(B0(A)), E).L).Elr.enc GL(BLR(B0(A)), E).L.lr.
       by inline{2} GL(B(BLR(A)), E).L.lr;sim.
       by proc (={glob LRB,C.c}).
       by proc (={glob LRB,C.c}).
       by proc (={glob LRB,C.c}).
     conseq (_ : _ ==> ={glob A, glob E, glob LRB, C.c}) => //;sim.
   cut -> : Pr[GR(BLR(B0(A)), E).main() @ &m :
              p' (glob A){hr} (glob E){hr} LRB.l res /\ C.c <= 1] = 
            Pr[GR(B(BLR(A)), E).main() @ &m :
              p' (glob A){hr} (glob E){hr} LRB.l res /\ C.c <= 1].
     byequiv (_: ={glob A, glob E} ==> ={glob A, glob E, LRB.l, C.c, res}) => //.
     proc.
     inline{1} GR(BLR(B0(A)), E).A.run BLR(B0(A), E, GR(BLR(B0(A)), E).R).A.run.
     inline{2} GR(B(BLR(A)), E).A.run B(BLR(A), E, GR(B(BLR(A)), E).R).A.run;wp.
     call (_: ={glob E, glob LRB, C.c}).
       proc;inline{2} LRB(E, GR(B(BLR(A)), E).R).lr;sim;sp.
       if => //;first by sim.
       if => //;last by call (_: true) => //;sim.
       inline{1} BLR(B0(A), E, GR(BLR(B0(A)), E).R).Elr.enc GR(BLR(B0(A)), E).R.lr.
       inline{2} GR(B(BLR(A)), E).R.lr.
       by inline C.incr;wp;call (_:true);wp.
       by proc (={glob LRB,C.c}).
       by proc (={glob LRB,C.c}).
       by proc (={glob LRB,C.c}).
     conseq (_ : _ ==> ={glob A, glob E, glob LRB, C.c}) => //;sim.
   clear p2; apply (Hybrid E (<:BLR(A)) _ _ _ _ _ &m p) => //.
   intros E0 LR Hlr HI HL HE;proc.
   call (_: true => true) => //.
   by proc;call Hlr.
  qed.

end Hybrid.
