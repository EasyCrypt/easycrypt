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
    fun work(x:input) : output
  }.

  module Rand (W:Worker) = {
    fun randAndWork() : input * output = {
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
  bdhoare_deno (_: (glob A) = (glob A){m} ==> 
                   ev (fst res) (glob A) (snd res) /\ fst res = v) => //.
  pose pr := Pr[A.work(v) @ &m: ev v (glob A) res];
  conseq* (_: _: = (mu_x d v * pr)). (* WEIRD! *)
  fun; seq 1 : (v = x) (mu_x d v) pr 1%r 0%r ((glob A)=(glob A){m})=> //.
    by rnd.
    by rnd; skip; progress=> //; rewrite /mu_x; apply mu_eq.
    call (_: (glob A) = (glob A){m} /\ x = v ==> 
             ev v (glob A) res) => //.
    simplify pr; bypr => &m' eqGlob.
    by equiv_deno (_: ={glob A, x} ==> ={res, glob A}) => //; fun true. 
    by conseq* (_: _ ==> false)=> //.
  qed.

  lemma introOrs (A <: Worker) &m (ev:input -> glob A -> output -> bool):
    Finite.finite (create (support d)) =>
    let sup = Finite.toFSet (create (support d)) in
    Pr[Rand(A).randAndWork() @ &m: ev (fst res) (glob A) (snd res)] =
     Pr[Rand(A).randAndWork() @ &m:
          cpOrs (img (lambda v r, ev v (glob A) (snd r) /\ v = fst r) sup) res].
  proof strict.
  intros=> Fsup sup.
  equiv_deno (_: ={glob A} ==> ={glob A, res} /\ in_supp (fst res{1}) d)=> //;
    first by fun; call (_: true); rnd.
  intros=> &m1 &m2 [[<- <-] Hin].
  rewrite /cpOrs or_exists;split.
    intros=> H.
    exists (lambda r, 
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
       (lambda (v:input), mu_x d v * Pr[A.work(v)@ &m:ev v (glob A) res]) 
       sup.
  proof strict.
  intros=> Fsup /=.
  cut:= introOrs A &m ev _=> //= ->.
  elim/set_ind (Finite.toFSet (create (support d))).
    rewrite Mrplus.sum_empty.
    bdhoare_deno (_ : true ==> false)=> //.
    by rewrite /cpOrs img_empty Mbor.sum_empty.
    intros=> x s Hx Hrec.
    rewrite Mrplus.sum_add //=.
    cut ->: Pr[Rand(A).randAndWork() @ &m:
                 cpOrs (img (lambda (v : input) (r : input * output),
                               ev v (glob A) (snd r) /\ v = fst r) (add x s)) res] =
             Pr[Rand(A).randAndWork() @ &m:
                 (ev x (glob A) (snd res) /\ x = fst res) \/
                 cpOrs (img (lambda (v : input) (r : input * output),
                               ev v (glob A){hr} (snd r) /\ v = fst r) s) res].
      rewrite Pr mu_eq => // &m1.
      pose f:= (lambda (v : input) (r : input * output),
                  ev v (glob A){m1} (snd r) /\ v = fst r).
      rewrite img_add.
      (* bug rewrite cpOrs_add: we are trying to rewrite a partially applied function *)
      cut ->: cpOrs (add (f x) (img f s)) == (cpOr (f x) (cpOrs (img f s))); last by smt.
      by rewrite cpOrs_add.       
    rewrite Pr mu_disjoint; first by smt.
    by rewrite Hrec (prCond A &m x ev).
  qed.

  lemma Mean_uni (A<:Worker) &m (ev:input -> glob A -> output -> bool) r: 
     (forall x, in_supp x d => mu_x d x = r) =>
     Finite.finite (create (support d)) =>
     let sup = Finite.toFSet (create (support d)) in
     Pr[Rand(A).randAndWork()@ &m: ev (fst res) (glob A) (snd res)] =
       r * Mrplus.sum (lambda (v:input), Pr[A.work(v)@ &m:ev v (glob A) res]) sup.
  proof.
    intros Hd Hfin /=.
    cut := Mean A &m ev => /= -> //.
    cut := Mrplus.sum_comp (( * ) r) (lambda (v:input), Pr[A.work(v)@ &m:ev v (glob A) res]) => /= <-.
      by intros x y;ringeq.
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
    pose ev := lambda (b:bool) (gA:glob A) (b':bool), b = b'.
    cut -> : Pr[Rand(A).randAndWork() @ &m : fst res = snd res] =
             Pr[Rand(A).randAndWork() @ &m : ev (fst res) (glob A) (snd res)] by trivial.
    cut Hcr: forall x, 
               mem x (create (support {0,1})) <=>
               mem x (add true (add false (FSet.empty)%FSet)) by smt.
    cut Hf : Finite.finite (create (support {0,1})).
      by exists (FSet.add true (FSet.add false FSet.empty)) => x;apply Hcr.
    cut := Mean A &m ev => /= -> //.
    cut -> : 
      Finite.toFSet (create (support {0,1})) = (FSet.add true (FSet.add false FSet.empty)).
      by apply FSet.set_ext => x; rewrite Finite.mem_toFSet //;apply Hcr.
    rewrite Mrplus.sum_add;first smt.
    rewrite Mrplus.sum_add;first smt.
    rewrite Mrplus.sum_empty /= !Bool.Dbool.mu_x_def;simplify ev.
    cut Hd: 2%r <> zero by smt.
    cut -> : Pr[A.work(true) @ &m : true = res] = Pr[A.work(true) @ &m : res].
      by rewrite Pr mu_eq;smt.
    cut -> : Pr[A.work(false) @ &m : false = res] = Pr[A.work(false) @ &m : !res].
      by rewrite Pr mu_eq;smt.       
    rewrite Pr mu_not.
    by rewrite Hloss;fieldeq.
  save.

end LR.

theory Hybrid.
  type input.
  type output.
  type leaks.
  op in0 : input.

  module type Enc = { 
    fun init () : unit { * }
    fun leaks () : leaks  
    fun enc (m:input) : output
  }.

  module type AEnc = {
    fun leaks () : leaks  
    fun enc (m:input) : output
  }.

  module type LR = { 
    fun lr(m0 m1:input) : output
  }.
   
  module L(E:Enc) = {
    fun lr(m0 m1:input) : output = {
      var r : output;
      r = E.enc(m0);
      return r;
    }
  }.

  module R(E:Enc) = {
    fun lr(m0 m1:input) : output = {
      var r : output;
      r = E.enc(m1);
      return r;
    }
  }. 

  module type E0Adv(E:AEnc, E0:AEnc) = {
    fun run () : bool
  }.

  import Int.

  module C = { 
    var c : int
    fun init () : unit = {
      c = 0;
    }
    fun incr () : unit = {
      c = c + 1;
    }
  }.

  module G_E (A:E0Adv, E:Enc) = {
    module Em = {
      fun leaks () : leaks = { (* TODO: be able to write fun leaks = E.leaks *)
        var r : leaks;
        r = E.leaks();
        return r;
      }

      fun enc(m:input) : output = {
        var r : output;
        r = E.enc(m);
        C.incr();
        return r;
      }
    }
      
    module A = A(E,Em)

    fun main () : bool = {
      var b' : bool;
      E.init();
      C.init();
      b' = A.run();
      return b';
    }
  }.

  module G_E0(A:E0Adv, E:Enc) = {
    module E0 = {
      
      fun leaks () : leaks = { (* TODO: be able to write fun leaks = E.leaks *)
        var r : leaks;
        r = E.leaks();
        return r;
      }

      fun enc(m:input) : output = {
        var r : output;
        r = E.enc(in0);
        C.incr();
        return r;
      }
    }
    module A = A(E,E0)

    fun main () : bool = {
      var b' : bool;
      E.init();
      C.init();
      b' = A.run();
      return b';
    }
  }.

  module type LRAdv(E:AEnc, LR:LR) = {
    fun run () : bool
  }.

  module GL(A:LRAdv, E:Enc) = {
    module L = { 
      fun lr(m0 m1:input) : output = {
        var r : output;
        r = E.enc(m0);
        C.incr();
        return r;
      }
    }
    module A = A(E,L)
    fun main () : bool = {
      var b' : bool;
      E.init();
      C.init();
      b' = A.run();
      return b';
    }
  }.

  module GR(A:LRAdv, E:Enc) = {
    module R = {
      fun lr(m0 m1:input) : output = {
        var r : output;
        r = E.enc(m1);
        C.incr();
        return r;
      }
    }
    module A = A(E,R)
    fun main () : bool = {
      var b' : bool;
      E.init();
      C.init();
      b' = A.run();
      return b';
    }
  }.

  module BLR(A:E0Adv, E:AEnc, LR:LR) = {
    module E0 = {
      fun leaks () : leaks = { (* TODO: be able to write fun leaks = E.leaks *)
        var r : leaks;
        r = E.leaks();
        return r;
      }

      fun enc(m:input) : output = {
        var r : output;
        r = LR.lr(m, in0);
        return r;
      }
    }
    module A = A(E,E0)
    fun run () : bool = {
      var b' : bool;
      b' = A.run();
      return b';
    }
  }.

  equiv Cinit : C.init ~ C.init : true ==> ={C.c}.
  proof strict.
   by fun;wp.
  qed.

  equiv Cincr : C.incr ~ C.incr : ={C.c} ==> ={C.c}.
  proof strict.
    by fun;wp.
  qed.

 
  section. (* E0_LR. *)
    declare module E : Enc{C}.
    declare module A : E0Adv{E,C}.

    equiv GE_GL : G_E(A,E).main ~ GL(BLR(A),E).main : ={glob A} ==> ={res,glob A,C.c}.
    proof strict.
      fun;inline{2} GL(BLR(A), E).A.run;wp.
      call (_: ={glob E, C.c}).
        by fun;call (_: true).
        fun;inline{2} GL(BLR(A), E).L.lr;wp.
        by call Cincr; call(_: true);wp.
        by fun (={C.c}).
        by fun (={C.c}).
      by call Cinit;call (_ : true).
    qed.

    equiv GE0_GR : G_E0(A,E).main ~ GR(BLR(A),E).main : ={glob A} ==> ={res,glob A}.
    proof strict.
      fun;inline{2} GR(BLR(A), E).A.run;wp.
      call (_: ={glob E,C.c}).
        by fun;call (_: true).
        fun; inline{2} GR(BLR(A), E).R.lr;wp.
        by call Cincr; call(_: true);wp.
        by fun (={C.c}).
        by fun (={C.c}).
      by call Cinit;call (_ : true).
    qed.

    lemma E0_LR &m (p:glob A -> bool): 
      Pr[G_E(A,E).main() @ &m : res /\ p (glob A) ] - 
      Pr[G_E0(A,E).main() @ &m : res /\ p (glob A) ] =
      Pr[GL(BLR(A),E).main() @ &m : res /\ p (glob A)] -
      Pr[GR(BLR(A),E).main() @ &m : res /\ p (glob A)].
    proof.
      congr;first by equiv_deno GE0_GR.
      by equiv_deno GE_GL.
    qed.

  end section.

   module LRB (E:AEnc,LR:LR) = {
    var l, l0 : int  
    fun lr(m0 m1:input):output = {
      var r : output;
      if (l0 < l) r = E.enc(m0);
      else { 
        if (l0 = l) r = LR.lr(m0,m1);
        else r = E.enc(m1);
      }
      l = l + 1;
      return r;
    }

      fun enc(m:input) : output = {
        var r : output;
        r = E.enc(in0);
        C.incr();
        return r;
      }
    
  }.
  
  op q : int.
  
  module B(A:LRAdv, E:AEnc, LR0:LR) = {
    module LR = LRB(E,LR0)
    module A = A(E,LR)
    fun run():bool = {
      var b':bool;
      LRB.l0 = $[0..q-1];
      LRB.l  = 0;
      b' = A.run();
      return b' && LRB.l <= q;
    }
  }.

  clone import Mean as M with
    type input <- int,
    type output <- bool,
    op d <- [0..q-1].

  section.

    declare module E    : Enc   {C,LRB}.
    declare module A    : LRAdv   {C,LRB,E}.

    local module W (LR0:LR) = {
      module LR = LRB(E,LR0)
      module A = A(E,LR)
      fun work(x:int) : bool = {
        var b':bool;
        LRB.l = 0; LRB.l0 = x;
        E.init();
        b' = A.run();
        return b' /\ LRB.l <= q;
      }
    }.

    local equiv Einit : E.init ~ E.init : true ==> ={glob E}.
    proof strict. by fun true. qed.

    local equiv Eleaks : E.leaks ~ E.leaks : ={glob E} ==> ={res,glob E}.
    proof strict. by fun true. qed.

    local equiv Eenc : E.enc ~ E.enc : ={m,glob E} ==> ={res,glob E}.
    proof strict. by fun true. qed.

    local lemma GLB_WL &m :
      Pr[GL(B(A),E).main() @ &m : res /\ C.c <= 1] = 
      Pr[Rand(W(L(E))).randAndWork() @ &m : snd res].
    proof strict.
      equiv_deno (_ : ={glob A} ==> res{1} = snd res{2} /\ C.c{1} <= 1) => //.
      fun; inline{1} GL(B(A), E).A.run;inline{2} W(L(E)).work;wp.
      call (_: ={glob E, glob LRB} /\ C.c{1} = (LRB.l0{1} < LRB.l{1}) ? 1 : 0).
        fun;wp.
        if => //;first by call Eenc;skip;progress => //; smt.
        if => //.
          inline{1} GL(B(A), E).L.lr C.incr;inline{2} L(E).lr.
          by wp;call Eenc;wp;skip;progress => //;smt.
        by call Eenc;skip;progress => //; smt.
        by conseq * Eleaks.
        by conseq * Eenc.
      swap{1} 1 3;inline{1} C.init.
      by call Einit;wp;rnd;wp;skip;progress => //;smt.
    qed.

    local lemma GRB_WR &m :
      Pr[GR(B(A),E).main() @ &m : res /\ C.c <= 1] = 
      Pr[Rand(W(R(E))).randAndWork() @ &m : snd res].
    proof strict.
      equiv_deno (_ : ={glob A} ==> 
                      res{1} = snd res{2} /\ C.c{1} <= 1) => //.
      fun; inline{1} GR(B(A), E).A.run;inline{2} W(R(E)).work;wp.
      call (_: ={glob E, glob LRB} /\ C.c{1} = (LRB.l0{1} < LRB.l{1}) ? 1 : 0).
        fun;wp.
        if => //;first by wp;call Eenc;skip;progress => //; smt.
        if => //.
          inline{1} GR(B(A), E).R.lr C.incr;inline{2} R(E).lr.
          by wp;call Eenc;wp;skip;progress => //;smt.
        by call Eenc;skip;progress => //; smt.
        by conseq * Eleaks.
        by conseq * Eenc.
      swap{1} 1 3;inline{1} C.init.
      by call Einit;wp;rnd;wp;skip;progress => //;smt.
    save.

    axiom losslessA (E0 <: AEnc{A}) (LR <: LR{A}):
        islossless LR.lr =>
        islossless E0.leaks => islossless E0.enc => islossless A(E0, LR).run.
    axiom losslessL: islossless E.leaks.
    axiom losslessE: islossless E.enc.

    axiom q_pos : 0 < q.

    local lemma WL0_GLA &m: 
       Pr[W(L(E)).work(0) @ &m : res] = Pr[GL(A,E).main() @ &m : res /\ C.c <= q ].
    proof strict.
      equiv_deno (_ : ={glob A} /\ x{1}=0 ==> 
                      res{1} = (res{2} /\ C.c{2} <= q)) => //.
      fun.
      call (_: q < C.c,
               ={glob E} /\ LRB.l0{1} = 0 /\ LRB.l{1} = C.c{2} /\ 0 <= LRB.l{1},
               LRB.l0{1} = 0 /\ q < LRB.l{1}).
        by apply losslessA.

        fun;inline{2} C.incr;wp.
        if{1};first by call Eenc;skip;progress => //;smt.
        rcondt{1} 1; first by intros &m0;skip;smt.
        by inline{1} L(E).lr;wp;call Eenc;wp;skip;progress => //;smt.
        intros &m2 _;fun.
        rcondt 1; first by skip;smt.
        by wp;call losslessE;skip;smt.
        by intros &m1;fun;inline C.incr;wp;call losslessE;wp;skip;smt.

        by conseq * Eleaks.
        intros &m2 _;conseq * losslessL.
        intros &m1; conseq * losslessL.

        by conseq * Eenc.
        intros &m2 _;conseq * losslessE.
        intros &m1; conseq * losslessE.

      by inline{2} C.init;wp;call Einit;wp;skip;progress => //;smt.
    qed.

    local lemma WRq_GRA &m: 
       Pr[W(R(E)).work((q-1)) @ &m : res] = Pr[GR(A,E).main() @ &m : res /\ C.c <= q ].
    proof strict.
      equiv_deno (_ : ={glob A} /\ x{1}=q-1 ==> 
                      res{1} = (res{2} /\ C.c{2} <= q)) => //.
      fun.
      call (_: q < C.c,
               ={glob E} /\ LRB.l0{1} = q-1 /\ LRB.l{1} = C.c{2} /\ 0 <= LRB.l{1},
               LRB.l0{1} = q-1 /\ q < LRB.l{1}).
        by apply losslessA.

        fun;inline{2} C.incr;wp.
        if{1};first by call{1} losslessE;call{2} losslessE;skip; smt.
        inline{1} R(E).lr;if{1};first by wp;call Eenc;wp;skip;progress => //;smt.
        by call Eenc;skip;progress => //;smt.
        intros &m2 _;fun.
        rcondt 1; first by skip;smt.
        by wp;call losslessE;skip; smt.
        by intros &m1;fun;inline C.incr;wp;call losslessE;wp;skip;smt.

        by conseq * Eleaks.
        intros &m2 _;conseq * losslessL.
        intros &m1; conseq * losslessL.

        by conseq * Eenc.
        intros &m2 _;conseq * losslessE.
        intros &m1; conseq * losslessE.

      by inline{2} C.init;wp;call Einit;wp;skip;progress => //;smt.
    qed.

    local lemma WLR_shift &m v: 1 <= v <= q-1 => 
         Pr[W(L(E)).work(v) @ &m: res] = Pr[W(R(E)).work((v-1)) @ &m : res].
    proof strict.
      intros Hv;equiv_deno (_: ={glob A} /\ x{1} = v /\ x{2} = v-1 ==> ={res}) => //.
      fun.
      call (_: ={glob E, LRB.l} /\ LRB.l0{1} = v /\ LRB.l0{2} = v-1).
        fun.
        if{1}; first by rcondt{2} 1;[intros &m0;skip;smt | wp;call Eenc].
        if{1};first by rcondt{2} 1;[intros &m0;skip;smt | inline{1} L(E).lr;wp;call Eenc;wp].
        rcondf{2} 1;first by intros &m0;skip;smt.
        by inline{2} R(E).lr;if{2};wp;call Eenc;wp.
        by conseq * Eleaks.
        by conseq * Eenc.
      by call Einit;wp.
    qed.

    (* TODO : move this *)
    lemma Mrplus_inter_shift (i j k:int) f: 
        Mrplus.sum f (Interval.interval i j) = 
        Mrplus.sum (lambda l, f (l + k)) (Interval.interval (i-k) (j-k)).
    proof strict.
      rewrite (Mrplus.sum_chind f (lambda l, l - k) (lambda l, l + k)) /=;first smt.
      congr => //.   
      apply FSet.set_ext => x.
      rewrite img_def Interval.mem_interval;split.
        intros [y];rewrite Interval.mem_interval;smt.
      intros Hx;exists (x+k);rewrite Interval.mem_interval;smt.
    qed.

    lemma Hybrid &m : 
       Pr[GL(B(A),E).main() @ &m : res /\ C.c <= 1] - 
         Pr[GR(B(A),E).main() @ &m : res /\ C.c <= 1] = 
       1%r/q%r * (
         Pr[GL(A,E).main() @ &m : res /\ C.c <= q] - 
           Pr[GR(A,E).main() @ &m : res /\ C.c <= q]).
    proof strict.
      rewrite (GLB_WL &m) (GRB_WR &m) -(WL0_GLA &m) -(WRq_GRA &m).
      cut Hint : Finite.(==) (create (support [0..q - 1])) (Interval.interval 0 (q - 1)).
        by intros x;rewrite mem_create Interval.mem_interval /support Dinter.supp_def.
      cut Hfin: Finite.finite (create (support [0..q - 1])).
        by exists (Interval.interval 0 (q-1)).
      cut Huni : forall (x : int), in_supp x [0..q - 1] => mu_x [0..q - 1] x = 1%r / q%r.
        by intros x Hx;rewrite Dinter.mu_x_def_in //;smt.
      cut := M.Mean_uni (W(L(E))) &m (lambda j g r, r) (1%r/q%r) _ _ => // /= ->.
      cut := M.Mean_uni (W(R(E))) &m (lambda j g r, r) (1%r/q%r) _ _ => // /= ->.
      cut -> : Finite.toFSet (create (support [0..q - 1])) = Interval.interval 0 (q-1).
        apply FSet.set_ext => x.
        by rewrite Interval.mem_interval Finite.mem_toFSet // 
             mem_create /support Dinter.supp_def.
      rewrite {1}Interval.interval_addl;first by smt.
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
      intros x; rewrite Interval.mem_interval => Hx;rewrite (WLR_shift &m x) //.
        (* cut -> : x + -1 = x - 1     BUG *) 
      by smt.
    qed.

  end section.
(*
print axiom Hybrid.

  lemma Hybrid0 (E <: Enc{C, LRB}) (A <: E0Adv{C, LRB, E}) : 
    (forall (E0 <: AEnc{A}) (LR <: LR{A}),
       islossless LR.lr =>
       islossless E0.leaks => islossless E0.enc => islossless A(E0, LR).run) => *)
    islossless E.leaks =>
    islossless E.enc =>
    0 < q =>
    forall &m,
      Pr[G_E(B(BLR(A), E).main() @ &m : res /\ C.c <= 1] -
      Pr[G_E0(B(A), E).main() @ &m : res /\ C.c <= 1] =
      1%r / q%r *
      (Pr[GL(A, E).main() @ &m : res /\ C.c <= q] -
       Pr[GR(A, E).main() @ &m : res /\ C.c <= q]).

lemma E0_LR:  &m (p:glob A -> bool): 
      Pr[G_E(A,E).main() @ &m : res /\ p (glob A) ] - 
      Pr[G_E0(A,E).main() @ &m : res /\ p (glob A) ] =
      Pr[GL(BLR(A),E).main() @ &m : res /\ p (glob A)] -
      Pr[GR(BLR(A),E).main() @ &m : res /\ p (glob A)].
*)
