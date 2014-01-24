require import Int.
require import Real.
require import Distr.
require import List.
require import FMap.

(*** Some type definitions *)
(** Our PRG uses a type for internal seeds
    and a type for its actual output. *)
type seed.

op dseed: seed distr.
axiom dseedL: mu dseed True = 1%r.

type output.

op dout: output distr.
axiom doutL: mu dout True = 1%r.

(** We use a PRF that, on input a seed, produces a seed and an output... *)
module type PRF = {
  proc * init()  : unit
  proc f (x:seed): seed * output
}.

(** ... to build a PRG that produces random output without requiring new input... *)
module type PRG = {
  proc * init(): unit (* We let our PRG have internal state, which we should be able to initialize *)
  proc prg ()  : output
}.

(*** Defining security *)
(** Distinguishers can call
    the PRG at most qP times and
    the PRF at most qF times and
    return a boolean *)
op qP:int.
axiom leq0_qP: 0 <= qP.

op qF:int.
axiom leq0_qF: 0 <= qF.

module type Adv (F:PRF,P:PRG) = {
  proc a(): bool { F.f P.prg } (* We do not let the adversary call the initialization oracles *)
}.

module Exp (A:Adv,F:PRF,P:PRG) = {
  module A = A(F,P)

  proc main():bool = {
    var b: bool;

    F.init();
    P.init();
    b = A.a();
    return b;
  }
}.

(** A PRG is secure iff it is indistinguishable from
    sampling in $dout by an adversary with access to the PRF
    and the PRG interfaces *)
module PrgI = {
  proc init () : unit = { }

  proc prg(): output = {
    var r;

    r = $dout;
    return r;
  }
}.

(*** Concrete considerations *)
(** We use the following PRF *)
module F = {
  var m:(seed,seed * output) map

  proc init(): unit = {
     m = empty;
  }

  proc f (x:seed) : seed * output = {
    var r1, r2;

    r1 = $dseed;
    r2 = $dout;
    if (!in_dom x m)
      m.[x] = (r1,r2);

    return oget (m.[x]);
  }
}.

lemma FfL: islossless F.f.
proof.
by proc; wp; do!rnd (True);
   skip; smt.
qed.

(** And we are proving the security of the following PRG *)
module P (F:PRF) = {
  var seed: seed

  proc init(): unit = {
    seed = $dseed;
  }

  proc prg(): output = {
    var r;

    (seed,r) = F.f (seed);
    return r;
  }
}.

(*** The Proof ***)
section.
  declare module A:Adv {P,F}.
  axiom AaL (F <: PRF {A}) (P <: PRG {A}):
    islossless F.f =>
    islossless P.prg =>
    islossless A(F,P).a.

  (** Adding some logging so we can express the bad event *)
  local module Plog = {
    var seed:seed
    var logP:seed list

    proc init(): unit = {
      seed = $dseed;
      logP = [];
    }

    proc prg(): output = {
      var r;

      logP = seed :: logP;
      (seed,r) = F.f(seed);
      return r;
    }
  }.

  local lemma P_Plog &m:
    Pr[Exp(A,F,P(F)).main() @ &m: res] = Pr[Exp(A,F,Plog).main() @ &m: res].
  proof.
  byequiv (_: ={glob A} ==> ={res})=> //.
  by do !sim.
  qed.

  pred Bad logP (m:('a,'b) map) =          (* Bad holds whenever: *)
       !unique logP                        (*  - there is a cycle in the state, OR *)
    \/ exists r, mem r logP /\ in_dom r m. (*  - an adversary query collides with an internal seed. *)

  lemma notBad logP (m:('a,'b) map):
    !Bad logP m <=>
      (unique logP /\ forall r, !mem r logP \/ !in_dom r m)
  by smt.

  (* In this game, we replace the PRF with fresh samples *)
  local module Psample = {
    proc init(): unit = {
      Plog.seed = $dseed;
      Plog.logP = [];
    }

    proc prg(): output = {
      var r1, r2;

      r1 = $dseed;
      r2 = $dout;
      Plog.logP = Plog.seed :: Plog.logP;
      Plog.seed = r1;
      return r2;
    }
  }.

  pred inv (m1 m2:('a,'b) map) logP =
    (forall r, in_dom r m1 <=> (in_dom r m2 \/ mem r logP)) /\
    (forall r, in_dom r m2 => m1.[r] = m2.[r]).

  local lemma Plog_Psample &m:
    Pr[Exp(A,F,Plog).main() @ &m: res] <=
      Pr[Exp(A,F,Psample).main() @ &m: res] +
      Pr[Exp(A,F,Psample).main() @ &m: Bad Plog.logP F.m].
  proof.
  apply (Trans _ (Pr[Exp(A,F,Psample).main() @ &m: res \/ Bad Plog.logP F.m]));
    last by rewrite Pr [mu_or]; smt.
  byequiv (_: ={glob A} ==> !(Bad Plog.logP F.m){2} => ={res})=> //; last smt.
  proc.
  call (_: Bad Plog.logP F.m, ={Plog.seed} /\ inv F.m{1} F.m{2} Plog.logP{2}).
    (* adversary is lossless *)
    by apply AaL.
    (* [F.f ~ F.f: I] when Bad does not hold *)
    by proc; wp; do !rnd; wp; skip; progress; smt.
    (* F.f is lossless when Bad holds *)
    by intros=> _ _; apply FfL.
    (* F.f preserves bad *)
    intros=> _ //=; proc.
    case (in_dom x F.m).
      by rcondf 3; do !rnd=> //; skip; smt.
    rcondt 3; first by do !rnd.
    by wp; do !rnd (True); skip; smt.
    (* [Psample.prg ~ Plog.prg: I] when Bad does not hold *)
    proc; inline F.f; swap{2} 3 -2.
    wp; do 2!rnd; wp; skip; progress; first 2 last; last 9 smt.
    by cut:= H8; rewrite notBad=> [logP_unique contradiction]; smt.
    (* Plog.prg is lossless when Bad holds *)
    by intros=> _ _; proc; inline F.f;
       wp; do 2!rnd (True); wp;
       skip; smt.
    (* Psample.prg preserves bad *)
    by intros=> _ //=; proc; wp; do 2!rnd; skip;
       progress; smt.
  (* Returning to main *)
  call (_: ={glob F} ==> ={glob Plog} /\ inv F.m{1} F.m{2} Plog.logP{2});
    first by proc; wp; rnd; skip; smt.
  call (_: true ==> ={glob F}); first by sim.
  by skip; smt.
  qed.

  local lemma Psample_PrgI &m:
    Pr[Exp(A,F,Psample).main() @ &m: res] = Pr[Exp(A,F,PrgI).main() @ &m: res].
  proof.
  byequiv (_: ={glob A} ==> ={res})=> //; proc.
  call (_: ={glob F})=> //.
    (* F.f *)
    by sim.
    (* Psample.prg ~ PrgI.prg *)
    by proc; wp; rnd; rnd{1}; wp; skip; smt.
  conseq* (_: _ ==> ={glob A, glob F})=> //.
  sim.
  by proc; wp; rnd{1}; skip; smt.
  qed.

  local lemma P_PrgI &m:
    Pr[Exp(A,F,P(F)).main() @ &m: res] <=
      Pr[Exp(A,F,PrgI).main() @ &m: res] + Pr[Exp(A,F,Psample).main() @ &m: Bad Plog.logP F.m].
  proof.
  by rewrite (P_Plog &m) -(Psample_PrgI &m) (Plog_Psample &m).
  qed.

  (** We now bound Pr[Exp(A,F,Psample).main() @ &m: Bad Plog.logP F.m] *)
  local module Resample = {
    proc resample() : unit = {
      var n, r;

      n = length Plog.logP;
      Plog.logP = [];
      Plog.seed = $dseed;
      while (length Plog.logP < n) {
        r = $dseed;
        Plog.logP = r :: Plog.logP;
      }
    }
  }.

  local module Exp' = {
    module A = A(F,Psample)

    proc main():bool = {
      var b : bool;
      F.init();
      Psample.init();
      b = A.a();
      Resample.resample();
      return b;
    }
  }.

  local lemma ExpPsample_Exp' &m:
    Pr[Exp(A,F,Psample).main() @ &m: Bad Plog.logP F.m] = Pr[Exp'.main() @ &m: Bad Plog.logP F.m].
  proof.
  byequiv (_: ={glob A} ==> ={Plog.logP, F.m})=> //; proc.
  transitivity{1} { F.init(); Psample.init(); Resample.resample(); b = Exp'.A.a(); }
     (={glob A} ==> ={F.m, Plog.logP}) 
     (={glob A} ==> ={F.m, Plog.logP})=> //.
    (* Equality on A's globals *)
    by intros=> &1 &2 A; exists (glob A){1}.
    (* no sampling ~ presampling *)
    sim; inline Resample.resample Psample.init F.init.
    rcondf{2} 7;
      first by intros=> _; rnd; wp; conseq (_: _ ==> true) => //.
    by wp; rnd; wp; rnd{2} (True); wp; skip; smt.
    (* presampling ~ postsampling *)
    seq 2 2: (={glob A, glob F, glob Plog}); first by sim.
    eager (H: Resample.resample(); ~ Resample.resample();: ={glob Plog, glob F} ==> ={glob Plog})
            : (={glob Plog, glob F, glob A})=> //;
      first by sim.
    eager proc H (={glob Plog, glob F})=> //.
      by eager proc; swap{1} 1 4; sim.
      by sim.
      eager proc; inline Resample.resample.
      swap{1} 3 3. swap{2} [4..5] 2. swap{2} [6..8] 1.
      swap{1} 4 3. swap{1} 4 2. swap{2} 2 4.
      sim.
      splitwhile (length Plog.logP < n - 1):{2} 5 .
      conseq* (_ : _ ==> ={Plog.logP})=> //.
      seq 3 5: (={Plog.logP} /\ (length Plog.logP = n - 1){2}).
        while (={Plog.logP} /\ n{2} = n{1} + 1 /\ length Plog.logP{1} <= n{1});
          first by wp; rnd; skip; progress; smt.
        by wp; rnd{2}; skip; progress=> //; smt.
      rcondt{2} 1; first by intros=> _; skip; smt.
      rcondf{2} 3; first by intros=> _; wp; rnd; skip; smt.
      by sim.
      by sim.
  qed.

(*
  lemma Bad_bound:
    phoare [Exp'.main : true ==> Bad Plog.logP F.m] <= ((qP*qF + (qP - 1)*qP/%2)%r*bd1).
  proof.
*)
end section.

(*
  (* We should now bound Pr[Exp(A,F,Psample).main() @ &m: Bad Plog.logP F.m] *)
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

axiom dsample1_uni : forall r, in_supp r dsample1 => mu_x dsample1 r = bd1.
axiom bd1_pos : 0%r <= bd1.
import FSet.
import ISet.Finite.

axiom qP_pos : 0 <= qP.
axiom qF_pos : 0 <= qF.

lemma Pr3 (A<:Adv{Prg,F,C}) : 
   bd_hoare [ Exp'(C(A)).main : true ==> bad Prg.logP F.m] <= ((qP*qF + (qP - 1)*qP/%2)%r*bd1).
proof.
  fun.
  seq 3 : true (1%r)  ((qP*qF + (qP - 1)*qP/%2)%r*bd1) 0%r 1%r  
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
         fun;wp;do !rnd;skip;progress => //. smt.
         rewrite dom_set;smt. smt.
        wp;skip;progress => //;smt.
      wp => //.
  inline F.init Prg_rB.init;wp;rnd;wp;skip;progress => //; smt.
  inline Resample.resample.
  exists * Prg.logP;elim * => logP0.
  seq 3 : true 
     1%r  ((qP*qF + (qP - 1)*qP/%2)%r*bd1)
     0%r 1%r 
         (finite (dom F.m) /\ n = length logP0 /\ n <= qP /\ Prg.logP = [] /\ 
          card (toFSet (dom F.m)) <= qF) => //.
    by rnd;wp.
    conseq (_:_: <= (if bad Prg.logP F.m then 1%r else 
                    ((sum_n (qF + length Prg.logP) (qF + n - 1))%r*bd1))).
      progress.
       rewrite (_:bad [] F.m{hr} = false); first rewrite /bad;smt.
      progress;apply CompatOrderMult => //;last smt.
      rewrite length_nil /=.
      generalize H0;elimT list_case logP0.
        rewrite length_nil /sum_n sum_ij_gt. smt.
        intros _. cut HqP : 0 <= (qP-1) * qP by smt.
        cut Hmod : 0 <= ( (qP - 1) * qP /% 2) by smt.
        by rewrite from_intMle;smt.
      intros x l H0;rewrite sumn_ij;first smt.
      rewrite ?FromInt.Add.
      apply addleM;first smt.
      rewrite from_intMle;apply ediv_Mle => //. 
      apply mulMle;smt.
    while{1} (finite (dom F.m) /\ n <= qP /\ card (toFSet (dom F.m)) <= qF).
      intros Hw.
      exists * Prg.logP, F.m, n;elim * => logP fm n0.
      case (bad Prg.logP F.m).
       conseq * ( _ : _ : <= (1%r)) => //. smt.
      seq 2 : (bad Prg.logP F.m) 
          ((qF + length logP)%r * bd1) 1%r
          1%r ((sum_n (qF + (length logP + 1)) (qF + n - 1))%r * bd1)
          (n = n0 /\ F.m = fm /\ finite (dom F.m) /\ r::logP = Prg.logP /\ 
          n <= qP /\ card (toFSet (dom F.m)) <= qF) => //.
        by wp;rnd => //.
        wp;rnd;skip;progress.
        generalize H3;rewrite !FromInt.Add Mul_distr_r /bad -rw_nor /= => [Hu He].
        apply (Real.Trans _ (mu dsample1 (cpOr (lambda x, in_dom x F.m{hr})
                                            (lambda x, mem x Prg.logP{hr})))).
          by apply mu_sub => x /=; rewrite /cpOr; smt.
        apply mu_or_le.
          rewrite (mu_eq _ _ (cpMem (toFSet (dom F.m{hr})))).
            by intros x; rewrite /= /cpMem;smt.
          by apply (Real.Trans _ ((card (toFSet (dom F.m{hr})))%r * bd1));smt.
        by apply mu_Lmem_le_length; smt.
        conseq Hw; progress => //.
        by rewrite (neqF ( bad (r{hr} :: logP) F.m{hr})) => //=; smt.
      progress => //.
      rewrite (neqF (bad Prg.logP{hr} F.m{hr}) _) => //=.
      rewrite -Mul_distr_r -Int.CommutativeGroup.Assoc -FromInt.Add sum_n_i1j //; smt.
    by skip;progress => //;smt.
save.

lemma conclusion_aux (A<:Adv{Prg,F,C}) :
    (forall (O1 <: AOrclPrg{A}) (O2<:OrclRnd{A}), islossless O1.prg => islossless O2.f => 
       islossless A(O1,O2).a) =>
    forall &m, 
      Pr[Exp(C(A),Prg).main() @ &m : res] <= 
        Pr[Exp(C(A),Prg_r).main() @ &m : res] +  (qP*qF + (qP - 1)*qP/%2)%r*bd1.
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
 cut _ : Pr[Exp'(C(A)).main() @ &m : bad Prg.logP F.m] <= (qP*qF + (qP - 1)*qP/%2)%r*bd1;
   last smt.
 bdhoare_deno (Pr3 A) => //.
save.

module NegA (A:Adv, P:AOrclPrg, R:OrclRnd) = {
  module A = A(P,R)
  fun a() : bool = { 
    var ba:bool;
    ba = A.a();
    return !ba;
  }
}.

lemma lossNegA (A<:Adv) :
  (forall (O1 <: AOrclPrg{A}) (O2 <: OrclRnd{A}),
     islossless O1.prg => islossless O2.f => islossless A(O1, O2).a) =>
  forall (O1 <: AOrclPrg{NegA(A)}) (O2 <: OrclRnd{NegA(A)}),
    islossless O1.prg => islossless O2.f => islossless NegA(A, O1, O2).a.
proof.
 intros Hloss O1 O2 HO1 HO2;fun.
 call (_:true) => //.
qed.

lemma NegA_Neg_main (P<:OrclPrg) (A<:Adv{P,F,C}) &m: 
    Pr[AdvAbsVal.Neg_main(Exp(C(A),P)).main() @ &m : res] =
    Pr[Exp(C(NegA(A)),P).main() @ &m : res].
proof.
  equiv_deno (_ : ={glob A, glob P, glob F} ==> ={res}) => //.
  fun.
  inline Exp(C(A), P).main Exp(C(NegA(A)), P).A.a C(NegA(A), P, F).A.a
     Exp(C(A), P).A.a;wp; eqobs_in.
qed.

lemma lossExp (P<:OrclPrg) (A<:Adv{P,F,C}):  
  (forall (O1 <: AOrclPrg{A}) (O2 <: OrclRnd{A}),
         islossless O1.prg => islossless O2.f => islossless A(O1, O2).a) =>
   islossless P.prg => islossless P.init =>
   islossless Exp(C(A),P).main.
proof.
 intros HA Hp Hi;fun.
 call (_: true).
   call (_: true) => //.
     fun.
     if;last by wp.
     by call Hp;wp.
     fun.
     if; last by wp.
     by call lossless_Ff;wp.
   by wp.
 call Hi.
 by call (_:true);first wp.
qed.

lemma conclusion (A<:Adv{Prg,F,C}) :
    (forall (O1 <: AOrclPrg{A}) (O2<:OrclRnd{A}), islossless O1.prg => islossless O2.f => 
       islossless A(O1,O2).a) =>
    forall &m, 
      `| Pr[Exp(C(A),Prg).main() @ &m : res] - Pr[Exp(C(A),Prg_r).main() @ &m : res] | <=  
       (qP*qF + (qP - 1)*qP/%2)%r*bd1.
proof.
 intros Hloss &m.
 case (Pr[Exp(C(A), Prg).main() @ &m : res] <= Pr[Exp(C(A), Prg_r).main() @ &m : res]) => Hle.
   cut H := conclusion_aux (NegA(A)) _ &m.
     by apply (lossNegA A).
   generalize H;rewrite -(NegA_Neg_main Prg A &m) -(NegA_Neg_main Prg_r A &m).
   rewrite (AdvAbsVal.Neg_A_Pr_minus (Exp(C(A), Prg)) &m).
     apply (lossExp Prg A) => //. 
       by fun;call lossless_Ff.
     fun;rnd;skip;smt.
   rewrite (AdvAbsVal.Neg_A_Pr_minus (Exp(C(A), Prg_r)) &m);last smt.
      apply (lossExp Prg_r A) => //. 
        by fun;rnd;skip;smt.
      by fun.
 by cut H := conclusion_aux A _ &m => //;smt.
save.

*)