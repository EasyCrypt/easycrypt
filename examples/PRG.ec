require import List.
require import Map.
require import Distr.
require import Int.
require import Real.
type t1.
type t2. 

op dsample1 : t1 distr.
op dsample2 : t2 distr.

module type OrclRnd = {
  fun f (x:t1) : t1 * t2
}.

module type AOrclPrg = {
  fun prg () : t2 
}.
 
module type OrclPrg = {
  fun init () : unit 
  fun prg () : t2 
}.
  
module type Adv (P:AOrclPrg,R:OrclRnd) = {
  fun a() : bool {P.prg R.f}
}.

op qF : int.
op qP : int.

module F = {
  var m : (t1, t1 * t2) map
  fun init() : unit = {
     m   = Map.empty;
  }
  fun f (x:t1) : t1 * t2 = {
    var r1 : t1;
    var r2 : t2;
    r1 = $dsample1;
    r2 = $dsample2;
    if (!in_dom x m) m.[x] = (r1,r2);
    return proj (m.[x]);
  }
}.

module Prg = {
  var logP : t1 list
  var seed : t1

  fun prg () : t2 = {
    var r:t2;
    (seed,r) = F.f (seed);
    return r;
  }

  fun init () : unit = {
    seed = $dsample1;
  }

}.

module Prg_r = {   

 fun prg() : t2 = {
    var r : t2;
    r = $dsample2;
    return r;
  }

  fun init () : unit = {
  }
   
}.
 
module Exp(A:Adv, Prg:OrclPrg) = {
  module A = A(Prg,F)

  fun main():bool = {
    var b : bool;
    F.init();
    Prg.init();
    b = A.a();
    return b;
  }
}.

module Prg_rB = {   

  fun prg() : t2 = {
    var r1 : t1;
    var r2 : t2;
    r1 = $dsample1;
    r2 = $dsample2;
    Prg.logP = Prg.seed :: Prg.logP;
    Prg.seed = r1; 
    return r2;
  }

  fun init () : unit = {
    Prg.seed = $dsample1;
    Prg.logP = [];
  }
   
}.

(* We prove :
    lemma 1 : Pr[G(A,Prg   ).main : res] <= 
              Pr[G(A,Prg_rB).main : res] + 
              Pr[G(A,Prg_rB).main : Bad(Prg.logP, Prg.mf)]
    lemma 2 : Pr[G(A,Prg_rB).main : res] = Pr[G(A,Prg_r).main : res]
  where Bad(Prg.logP, Prg.mf) = 
    !unique Prg.logP || exists r, mem r Prg.logP /\ in_dom r Prg.mf  
   We get  
       Pr[G(A,Prg   ).main : res] <= 
          Pr[G(A,Prg_r ).main : res] + 
          Pr[G(A,Prg_rB).main : Bad(Prg.logP, Prg.mf)]
   We conclude 
       | Pr[G(A,Prg   ).main : res] - Pr[G(A,Prg_r ).main : res] | <=
         Pr[G(A,Prg_rB).main : Bad(Prg.logP, Prg.mf)]
*)

axiom lossless1 : weight dsample1 = 1%r.
axiom lossless2 : weight dsample2 = 1%r.

pred bad logP (m:('a,'b) map) = !unique logP \/ exists r, mem r logP /\ in_dom r m.
pred inv (m1 m2:('a,'b) map) logP = 
   (*logP <> [] /\
   s = hd (logP) /\*)
   (forall r, in_dom r m1 <=> (in_dom r m2 \/ mem r logP)) /\
   (forall r, in_dom r m2 => m1.[r] = m2.[r]).

lemma lossless_Ff : islossless F.f.
proof.
  fun;wp;do !rnd;skip;progress;[apply lossless2 | apply lossless1].
save.

section.
  declare module A:Adv{Prg,F}. (* Since Prg use F, adding the restriction F redondant *)

  lemma equiv_rB : 
     (forall (O1 <: AOrclPrg{A}) (O2<:OrclRnd{A}), islossless O1.prg => islossless O2.f => 
        islossless A(O1,O2).a) =>
     equiv [Exp(A,Prg).main ~ Exp(A,Prg_rB).main :
            ={glob A} ==> !(bad Prg.logP F.m){2} => ={res}].
  proof.
    intros Hlossless;fun;call (_ : (bad Prg.logP F.m), ={Prg.seed} /\
                                inv F.m{1} F.m{2} Prg.logP{2}).  
    fun;inline F.f;wp;do !rnd;wp;skip.
    intros &m1 &m2 /= [Hnbad [-> [Hdom Hget]]] /= r1L r1R HinL1 HinR1;split;
     first by trivial.
    intros H => {H} r2L r2R HinL2 HinR2;split; first by trivial.
    intros H => {H};case (!in_dom Prg.seed{m2} F.m{m1}) => Hin; by smt.
    intros _ _;fun. call lossless_Ff => //.
    intros _;fun;wp;do !rnd;skip; progress;try smt. 

    fun;wp => /=; do !rnd;skip => /=.
    intros &m1 &m2 /= [Hnbad [-> [-> [Hdom Hget]]]] /= r1L r1R HinL1 HinR1;split;
    first by trivial.
    intros H => {H} r2L r2R HinL2 HinR2;split; first by trivial.
    intros H => {H};split => /= H1;split => H2 /=; last 3 smt.
    intros _;progress => //; try smt.
    intros _ _; apply lossless_Ff.
    intros _;fun;wp; conseq * (_ : _ ==> true) => /=.
    intros &hr Hb r1 r2;split => //=; smt.
     do !rnd;skip;progress; [apply lossless2 | apply lossless1].
    inline F.init Prg.init Prg_rB.init;wp;rnd;wp;skip;smt.
  save.   

  equiv equiv_rB_r : Exp(A,Prg_rB).main ~ Exp(A,Prg_r).main : 
     ={glob A} ==> ={res}.
  proof.
    fun;call (_ : ={F.m}).
    fun.
    wp;rnd;rnd{1};skip;progress => //;apply lossless1.
    fun;eqobs_in.
    conseq (_ : _ ==>  ={glob A, F.m}) => //.
    inline F.init Prg_rB.init Prg_r.init.
    wp;rnd{1};wp;skip;progress => //;apply lossless1.
  save.

 

  (* We should now bound the probability of bad *)
  (* For this we use eager/lazy, then we compute the probability. *)

  module Resample = {
    fun resample() : unit = {
      var n : int;
      var r : t1;
      n = length Prg.logP;
      Prg.logP = [];
      Prg.seed = $dsample1;  
      while (List.length Prg.logP < n) {
        r = $dsample1;
        Prg.logP = r :: Prg.logP;
      }
    }
  }.

  module Exp'(A:Adv) = {
  
    module A = A(Prg_rB,F)

    fun main():bool = {
      var b : bool;
      F.init();
      Prg_rB.init();
      b = A.a();
      Resample.resample();
      return b;
    }
  }.
  local module Exp1 =  Exp'(A).

  local equiv Exp_Exp' : Exp(A,Prg_rB).main ~ Exp1.main : ={glob A} ==> ={F.m, Prg.logP}.
  proof.
   fun.
   transitivity{1} { F.init(); Prg_rB.init();Resample.resample(); b = Exp1.A.a(); } 
     (={glob A} ==> ={F.m, Prg.logP}) 
     (={glob A} ==> ={F.m, Prg.logP});[smt | trivial | | ].
     eqobs_in;inline Resample.resample Prg_rB.init F.init.
     rcondf{2} 7.
       intros &m;rnd;wp. 
       conseq (_ : _ ==> true) => //.
     wp;rnd;wp;rnd{2};wp;skip;progress => //; apply lossless1.
   seq 2 2 : (={glob A, F.m, glob Prg_rB}); first by eqobs_in.
   eager (h : Resample.resample(); ~ Resample.resample(); 
         : ={Prg.logP} ==> ={Prg.logP, Prg.seed}) : 
         (={Prg.logP,F.m,Prg.seed,glob A}) => //.
   eqobs_in => //.
   eager fun h (={Prg.logP,F.m,Prg.seed}) => //.
   eager fun.
     inline Resample.resample.
     swap{1} 3 3. swap{2} [4..5] 2. swap{2} [6..8] 1.
     swap{1} 4 3. swap{1} 4 2. swap{2} 2 4.
     eqobs_in.
     splitwhile (length Prg.logP < n - 1) : {2} 5 .
     conseq * (_ : _ ==> ={Prg.logP}) => //.
     seq 3 5 : (={Prg.logP} /\ (length Prg.logP = n - 1){2}).
     while (={Prg.logP} /\ n{2} = n{1} + 1 /\ (length Prg.logP <= n){1}).
       wp;rnd;skip;progress => //;smt.
     wp;rnd{2};skip;progress => //; smt.
     rcondt{2} 1.
       intros &m;skip;smt.
     rcondf{2} 3;first intros &m;wp;rnd;skip;smt.
     eqobs_in.
   fun;eqobs_in.
   eager fun.
    swap{2} 5 -4;eqobs_in.
   fun;eqobs_in.
  save.

  lemma Pr1 : 
    (forall (O1 <: AOrclPrg{A}) (O2<:OrclRnd{A}), islossless O1.prg => islossless O2.f => 
       islossless A(O1,O2).a) =>
    forall &m, 
      Pr[Exp(A,Prg).main() @ &m : res] <= 
        Pr[Exp(A,Prg_r).main() @ &m : res] + 
        Pr[Exp'(A).main() @ &m : bad Prg.logP F.m].
  proof.
    intros Hll &m.
    apply (Real.Trans _ Pr[Exp(A,Prg_rB).main() @ &m : res \/ bad Prg.logP F.m]).
    equiv_deno (equiv_rB _) => //; smt.
    rewrite Pr mu_or.
    rewrite  (_:Pr[Exp(A, Prg_rB).main() @ &m : res] = Pr[Exp(A, Prg_r).main() @ &m : res]).
    equiv_deno equiv_rB_r => //.
    rewrite ( _: Pr[Exp(A, Prg_rB).main() @ &m : bad Prg.logP F.m] = Pr[Exp'(A).main() @ &m : bad Prg.logP F.m]);[ | smt].
    equiv_deno Exp_Exp' => //.
  save.

end section.

op default1 : t1.
op default2 : t2.

module C(A:Adv,P:AOrclPrg,R:OrclRnd) = {
    module CP = {
      var c : int
      fun prg () : t2 = {
        var r : t2;
        if (c < qP) { c = c + 1; r = P.prg();}
        else r = default2;
        return r;
      }
    }

    module CF = {
      var c : int 
      fun f (x) : t1 * t2 = {
        var r : t1*t2;
        if (c < qF) { c = c + 1; r = R.f(x);}
        else r = (default1,default2);
        return r;
      }
    } 
    
    module A = A(CP,CF)

    fun a() : bool = {
      var b:bool;
      CP.c = 0;
      CF.c = 0;
      b = A.a();
      return b;
    }
  }.

op bd1 : real.

axiom dsample1_uni : forall r, mu_x dsample1 r = bd1.
import FSet.
import ISet.Finite.

axiom qP_pos : 0 <= qP.
axiom qF_pos : 0 <= qF.

lemma Pr3 (A<:Adv{Prg,F,C}) : 
   bd_hoare [ Exp'(C(A)).main : true ==> bad Prg.logP F.m] <= (bd1 * ((qP + qF) * qP)%r).
proof.
  fun.
  seq 3 : true (1%r) (bd1 * ((qP + qF) * qP)%r) 0%r 1%r  
        (finite (dom F.m) /\ length Prg.logP <= qP /\ FSet.card (toFSet (dom F.m)) <= qF) => //.
    inline Exp'(C(A)).A.a;wp.
    call (_: finite (dom F.m) /\ length Prg.logP = C.CP.c /\ C.CP.c <= qP /\ 
             card (toFSet (dom F.m)) <= C.CF.c /\ C.CF.c <= qF).
      fun;if.
       call (_: length Prg.logP = C.CP.c - 1 ==> length Prg.logP = C.CP.c).
         fun;wp;do !rnd; skip; progress => //. smt.
       wp;skip;progress => //;smt.
      wp => //.
      fun;if.
        call (_: finite (dom F.m) /\ card (toFSet (dom F.m)) <= C.CF.c - 1 ==> 
                 finite (dom F.m) /\ card (toFSet (dom F.m)) <= C.CF.c).
         fun;wp;do !rnd;skip;progress => //; smt.
        wp;skip;progress => //;smt.
      wp => //.
  inline F.init Prg_rB.init;wp;rnd;wp;skip;progress => //; smt.
 
  inline Resample.resample.
    seq 3 : true 
       1%r (if bad Prg.logP F.m then 1%r 
            else  bd1 * ((qP + qF) * (n - length Prg.logP))%r) 
       0%r 1%r 
         (finite (dom F.m) /\ n <= qP /\ Prg.logP = [] /\ 
          card (toFSet (dom F.m)) <= qF) => //.
       rnd;wp => //.
    while{1} (finite (dom F.m) /\ n <= qP /\ card (toFSet (dom F.m)) <= qF).
    intros Hw.
    exists * Prg.logP, F.m, n;elim * => logP fm n0.
    case (bad Prg.logP F.m).
     conseq * ( _ : _ : <= (1%r)) => //; smt. 
    seq 2 : (bad Prg.logP F.m) 
      ((qP + qF)%r * bd1) 1%r
      1%r  (bd1 * ((qP + qF) * (n - (length logP + 1)))%r)
      (n = n0 /\ F.m = fm /\ finite (dom F.m) /\ r::logP = Prg.logP /\ 
       n <= qP /\ card (toFSet (dom F.m)) <= qF) => //.
     wp;rnd => //.
     wp;rnd;skip;progress.
     generalize H3;rewrite !FromInt.Add Mul_distr_r /bad -rw_nor /= => [Hu He].
     apply (Real.Trans _ (mu dsample1 (cpOr (lambda x, mem x Prg.logP{hr})
                                            (lambda x, in_dom x F.m{hr})))).
      apply mu_sub => x /=; rewrite /cpOr; smt.
     cut Hbd1 : 0%r <= bd1.
       cut _ := dsample1_uni default1;by smt.
     apply mu_or_le.
       apply (Real.Trans _ ((length Prg.logP{hr})%r * bd1)).
         by apply mu_Lmem_le_length; smt.
       apply CompatOrderMult => //;smt.
     rewrite (mu_eq _ _ (cpMem (toFSet (dom F.m{hr})))).
       intros x; rewrite /= /cpMem. smt.
     apply (Real.Trans _ ((card (toFSet (dom F.m{hr})))%r * bd1));smt.
    conseq Hw => //.
      progress => //.
      rewrite (neqF ( bad (r{hr} :: logP) F.m{hr})) => //=; smt.
    progress => //.
    rewrite (neqF (bad Prg.logP{hr} F.m{hr}) _) => //=.
    apply eq_le; ringeq.
    skip;progress => //. smt.
save.

lemma conclusion (A<:Adv{Prg,F,C}) :
    (forall (O1 <: AOrclPrg{A}) (O2<:OrclRnd{A}), islossless O1.prg => islossless O2.f => 
       islossless A(O1,O2).a) =>
    forall &m, 
      Pr[Exp(C(A),Prg).main() @ &m : res] <= 
        Pr[Exp(C(A),Prg_r).main() @ &m : res] +  bd1 * ((qP + qF) * qP)%r.
proof.
 intros HA &m.      
 apply (Real.Trans _ (Pr[Exp(C(A),Prg_r).main() @ &m : res] + 
        Pr[Exp'(C(A)).main() @ &m : bad Prg.logP F.m])).
 apply (Pr1 (<:C(A)) _ &m). 
 intros O1 O2 HO1 HO2;fun.
 call (HA (<:C(A,O1,O2).CP) (<:C(A,O1,O2).CF) _ _).
  fun;if;[call HO1 | ];wp => //.
  fun;if;[call HO2 | ];wp => //.
  wp => //.
 cut _ : Pr[Exp'(C(A)).main() @ &m : bad Prg.logP F.m] <= bd1 * ((qP + qF) * qP)%r;
   last smt.
 bdhoare_deno (Pr3 A) => //.
save.

