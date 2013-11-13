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

  module type Mk_LR(E:AEnc) = {
    fun lr(m0 m1:input) : output
  }.
    
(*  module L(E:Enc) = {
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
*)

  module type Adv(E:AEnc, LR:LR) = {
    fun run () : bool
  }.

  import Int.

  module N (E:Enc, LR:LR, A:Adv) = {
    var c:int

    module LRc = {
      fun lr(m0 m1:input) : output = {
        var r : output;
        c = c + 1;
        r = LR.lr(m0, m1);
        return r;
      }
    }

    module A = A(E,LRc)

    fun main () : bool = {
      var b' : bool;
      c = 0;        
      E.init();
      b' = A.run();
      return b';
    }
  }.

  op q : int.

  clone import Mean as M with
    type input <- int,
    type output <- bool,
    op d <- [0..q-1].

  module LRB (L: LR, R: LR, LR0:LR) = {
    var l, l0 : int  
    fun lr(m0 m1:input):output = {
      var r : output;
      if (l0 < l) r = L.lr(m0,m1);
      else { 
        if (l0 = l) r = LR0.lr(m0,m1);
        else r = R.lr(m0,m1);
      }
      l = l + 1;
      return r;
    }
  }.
 
  module B(A:Adv, L:LR, R:LR, E:AEnc, LR0:LR) = {
    module LR = LRB(L,R,LR0)
    module A = A(E,LR)
    fun run():bool = {
      var b':bool;
      LRB.l0 = $[0..q-1];
      LRB.l  = 0;
      b' = A.run();
      return b' && LRB.l <= q;
    }
  }.

  section.

  declare module E    : Enc   {N,LRB}.
  declare module ML   : Mk_LR {N,LRB,E}.
  declare module MR   : Mk_LR {N,LRB,E,ML}.  
  declare module A    : Adv   {N,LRB,E,ML,MR}.
  
  local module L   = ML(E).
  local module R   = MR(E).
  local module LRBL = LRB(L,R,L).
  local module LRBR = LRB(L,R,R).

  local module BA  = B(A, L, R).
  local module NLB = N(E,L,BA).
  local module NRB = N(E,R,BA).  


  local module W (LR0:LR) = {
    module LR = LRB(L,R,LR0)
    module A = A(E,LR)
    fun work(x:int) : bool = {
      var b':bool;
      LRB.l = 0; LRB.l0 = x;
      E.init();
      b' = A.run();
      return b' && LRB.l <= q;
    }
  }.

  local equiv Einit : E.init ~ E.init : true ==> ={glob E}.
  proof strict.
    by fun true.
  qed.

  local equiv Eleaks : E.leaks ~ E.leaks : ={glob E} ==> ={res,glob E}.
  proof strict.
    by fun true.   
  qed.

  local equiv Eenc : E.enc ~ E.enc : ={m,glob E} ==> ={res,glob E}.
  proof strict.
    by fun true.   
  qed.

  local equiv Eml : ML(E).lr ~ ML(E).lr : ={m0,m1,glob ML, glob E} ==> ={res, glob ML, glob E}.
  proof strict.
    fun (={glob E})=> //;[apply Eleaks | apply Eenc].
  qed.

  local equiv Emr : MR(E).lr ~ MR(E).lr : ={m0,m1,glob MR, glob E} ==> ={res, glob MR, glob E}.
  proof strict.
    fun (={glob E})=> //;[apply Eleaks | apply Eenc].
  qed.
 
  local lemma NWL &m :
    Pr[N(E,L,BA).main() @ &m : res /\ N.c <= 1] = 
    Pr[Rand(W(L)).randAndWork() @ &m : snd res].
  proof strict.
    equiv_deno (_ : ={glob A, glob ML, glob MR} ==> 
                    res{1} = snd res{2} /\ N.c{1} <= 1) => //.
    fun. 
    inline{1} N(E, ML(E), B(A, ML(E), MR(E))).A.run.
    inline{2} W(ML(E)).work;wp.
    call (_: ={glob ML, glob MR, glob E, glob LRB} /\ N.c{1} = (LRB.l0{1} < LRB.l{1}) ? 1 : 0).
      fun;wp.
      if => //.
        by call Eml;skip;progress => //; smt.
      if => //.
        inline{1} N(E, ML(E), B(A, ML(E), MR(E))).LRc.lr;wp.
        by call Eml;wp;skip;progress => //;smt.
      by call Emr;skip;progress => //; smt.
      by conseq * Eleaks.
      by conseq * Eenc.
    swap{1} 2 2.
    by call Einit;wp;rnd;wp;skip;progress => //;smt.
  qed.

  local lemma NWR &m :
    Pr[N(E,R,BA).main() @ &m : res /\ N.c <= 1] = 
    Pr[Rand(W(R)).randAndWork() @ &m : snd res].
  proof strict.
    equiv_deno (_ : ={glob A, glob ML, glob MR} ==> 
                    res{1} = snd res{2} /\ N.c{1} <= 1) => //.
    fun. 
    inline{1} N(E, MR(E), B(A, ML(E), MR(E))).A.run.
    inline{2} W(MR(E)).work;wp.
    call (_: ={glob ML, glob MR, glob E, glob LRB} /\ N.c{1} = (LRB.l0{1} < LRB.l{1}) ? 1 : 0).
      fun;wp.
      if => //.
        by call Eml;skip;progress => //; smt.
      if => //.
        inline{1} N(E, MR(E), B(A, ML(E), MR(E))).LRc.lr;wp.
        by call Emr;wp;skip;progress => //;smt.
      by call Emr;skip;progress => //; smt.
      by conseq * Eleaks.
      by conseq * Eenc.
    swap{1} 2 2.
    by call Einit;wp;rnd;wp;skip;progress => //;smt.
  save.

  axiom losslessA (E0 <: AEnc{A}) (LR <: LR{A}):
      islossless LR.lr =>
      islossless E0.leaks => islossless E0.enc => islossless A(E0, LR).run.
  axiom losslessML (E0 <: AEnc{ML}):
    islossless E0.leaks => islossless E0.enc => islossless ML(E0).lr.
  axiom losslessMR (E0 <: AEnc{MR}):
    islossless E0.leaks => islossless E0.enc => islossless MR(E0).lr.
  axiom losslessL: islossless E.leaks.
  axiom losslessE: islossless E.enc.

  local lemma losslessMLE : islossless ML(E).lr.
  proof strict.
    apply (losslessML E);[apply losslessL | apply losslessE].
  qed.

  local lemma losslessMRE : islossless MR(E).lr.
  proof strict.
    apply (losslessMR E);[apply losslessL | apply losslessE].
  qed.
  
  axiom q_pos : 0 < q.

  local lemma WL0_NLA &m: 
     Pr[W(L).work(0) @ &m : res] = Pr[N(E,L,A).main() @ &m : res /\ N.c <= q ].
  proof strict.
    equiv_deno (_ : ={glob A, glob ML, glob MR} /\ x{1}=0 ==> 
                    res{1} = (res{2} /\ N.c{2} <= q)) => //.
    fun.
    call (_: q < N.c,
             ={glob ML, glob MR, glob E} /\ LRB.l0{1} = 0 /\ LRB.l{1} = N.c{2} /\ 0 <= LRB.l{1},
             LRB.l0{1} = 0 /\ q < LRB.l{1}).
      by apply losslessA.

      fun.
      if{1}.
        by wp;call Eml;wp;skip;progress => //;smt.
      rcondt{1} 1.
        by intros &m0;skip;smt.
      by wp;call Eml;wp;skip;progress => //;smt.
      intros &m2 _;fun.
      rcondt 1; first by skip;smt.
      by wp;call losslessMLE;skip;smt.
      intros &m1;fun.
      by call losslessMLE;wp;skip;smt.
      
      by conseq * Eleaks.
      intros &m2 _;conseq * losslessL.
      intros &m1; conseq * losslessL.

      by conseq * Eenc.
      intros &m2 _;conseq * losslessE.
      intros &m1; conseq * losslessE.
    
    by call Einit;wp;skip;progress => //;smt.
  qed.

  local lemma WRq_NRA &m: 
     Pr[W(R).work((q-1)) @ &m : res] = Pr[N(E,R,A).main() @ &m : res /\ N.c <= q ].
  proof strict.
    equiv_deno (_ : ={glob A, glob ML, glob MR} /\ x{1}=q-1 ==> 
                    res{1} = (res{2} /\ N.c{2} <= q)) => //.
    fun.
    call (_: q < N.c,
             ={glob ML, glob MR, glob E} /\ LRB.l0{1} = q-1 /\ LRB.l{1} = N.c{2} /\ 0 <= LRB.l{1},
             LRB.l0{1} = q-1 /\ q < LRB.l{1}).
      by apply losslessA.

      fun.
      if{1}.
        by wp;call{1} losslessMLE;call{2} losslessMRE;wp;skip; smt.
      if{1}.
        by wp;call Emr;wp;skip;progress => //;smt.
      by wp;call Emr;wp;skip;progress => //;smt.
      intros &m2 _;fun.
      rcondt 1; first by skip;smt.
      by wp;call losslessMLE;skip; smt.
      by intros &m1;fun;call losslessMRE;wp;skip;smt.
      
      by conseq * Eleaks.
      intros &m2 _;conseq * losslessL.
      intros &m1; conseq * losslessL.

      by conseq * Eenc.
      intros &m2 _;conseq * losslessE.
      intros &m1; conseq * losslessE.
    
    by call Einit;wp;skip;progress => //;smt.
  qed.

  local lemma WLR_shift &m v: 1 <= v <= q-1 => 
       Pr[W(L).work(v) @ &m: res] = Pr[W(R).work((v-1)) @ &m : res].
  proof strict.
    intros Hv;equiv_deno (_: ={glob A, glob ML, glob MR} /\ x{1} = v /\ x{2} = v-1 ==> ={res}) => //.
    fun.
    call (_: ={glob ML, glob MR, glob E, LRB.l} /\ LRB.l0{1} = v /\ LRB.l0{2} = v-1).
      fun.
      if{1}.        
        rcondt{2} 1;first by intros &m0;skip;smt.
        by wp;call Eml.
      if{1}.
        rcondt{2} 1;first by intros &m0;skip;smt.
        by wp;call Eml.
      rcondf{2} 1;first by intros &m0;skip;smt.
      by if{2};wp;call Emr.
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
     Pr[N(E,ML(E),B(A,ML(E),MR(E))).main() @ &m : res /\ N.c <= 1] - 
        Pr[N(E,MR(E),B(A,ML(E),MR(E))).main() @ &m : res /\ N.c <= 1] = 
     1%r/q%r * (
       Pr[N(E,ML(E),A).main() @ &m : res /\ N.c <= q] - 
         Pr[N(E,MR(E),A).main() @ &m : res /\ N.c <= q]).
  proof strict.
    rewrite (NWL &m) (NWR &m) -(WL0_NLA &m) -(WRq_NRA &m).
    cut Hint : Finite.(==) (create (support [0..q - 1])) (Interval.interval 0 (q - 1)).
      by intros x;rewrite mem_create Interval.mem_interval /support Dinter.supp_def.
    cut Hfin: Finite.finite (create (support [0..q - 1])).
      by exists (Interval.interval 0 (q-1)).
    cut Huni : forall (x : int), in_supp x [0..q - 1] => mu_x [0..q - 1] x = 1%r / q%r.
      by intros x Hx;rewrite Dinter.mu_x_def_in //;smt.
    cut := M.Mean_uni (W(L)) &m (lambda j g r, r) (1%r/q%r) _ _ => // /= ->.
    cut := M.Mean_uni (W(R)) &m (lambda j g r, r) (1%r/q%r) _ _ => // /= ->.
    cut -> : Finite.toFSet (create (support [0..q - 1])) = Interval.interval 0 (q-1).
      apply FSet.set_ext => x.
      by rewrite Interval.mem_interval Finite.mem_toFSet // mem_create /support Dinter.supp_def.
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

end Hybrid.


