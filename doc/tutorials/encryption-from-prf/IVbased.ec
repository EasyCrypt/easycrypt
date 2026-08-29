require import AllCore List Distr FSet.
require (*  *) Construction Birthday.

(** Non-empty sets for keys, plaintexts and nonces **)
type key, ptxt, rndness.
type ctxt = ptxt.

(** Some (arbitrary, here) distribution over keys **)
op [lossless] dkey: key distr.

(** Some (arbitrary, here) distribution over randomness **) 
op [lossless full uniform] drndness: rndness distr.

(** Some (arbitrary, here) distribution over plaintexts/ciphertexts **) 
op [lossless full uniform] dptxt : ptxt distr.
op dctxt = dptxt.

(** And a family of functions from nonces to plaintexts, indexed by
    the set of keys **)
op f: key -> rndness -> ptxt.

(** Some associative, commutative, self-cancelling operator over
    plaintexts **)
op (+): ptxt -> ptxt -> ptxt.
axiom addpA x y z: x + y + z = x + (y + z).
axiom addpC x y: x + y = y + x.
axiom addKp x y: x + x + y = y.

lemma addpK x y: y + x + x = y.
proof. by rewrite addpA addpC addKp. qed.

(** The scheme!! **)
module type Enc_Scheme = {
  proc kgen(): key
  proc enc(k : key, r : rndness, m : ptxt): ctxt
  proc dec(k : key, r : rndness, c : ctxt): ptxt
}.

module E : Enc_Scheme = {
  proc kgen(): key = {
    var k;

    k <$ dkey;
    return k;
  }

  proc enc(k : key, r : rndness, m : ptxt) : ctxt = {
    var x;

    x <- f k r;
    return x + m;
  }

  proc dec(k : key, r : rndness, c : ctxt) : ptxt = {
    var x;

    x <- f k r;
    return x + c;
  }
}.

clone import Construction as C with
  type key <- key,
  type ptxt <- ptxt,
  type nonce <- rndness,
  op f <- f,
  op (+) <- (+),
  op dkey <- dkey,
  op dptxt <- dptxt
  (* Why can't I do E <- E, they are literally the same. I do not want duplicates. *)
proof *.
realize addpA by exact/addpA.
realize addpC by exact/addpC.
realize addKp by exact/addKp.
realize dptxt_ll by exact/dptxt_ll.
realize dptxt_uni by exact/dptxt_uni.
realize dptxt_fu by exact/dptxt_fu.

(** CPA security **)
module type CPA_Oracle_IV_i = {
  proc init(): unit
  proc enc(m : ptxt) : rndness * ctxt
}.

module O_IV_ideal : CPA_Oracle_IV_i = {
  proc init() : unit = {
  }

  proc enc(m : ptxt) : rndness * ctxt = {
    var r, c;

    r <$ drndness;
    c <$ dctxt;
    return (r, c);
  }
}.

module O_IV_real (E : Enc_Scheme) : CPA_Oracle_IV_i = {
  var k : key

  proc init() : unit = {
    k <@ E.kgen();
  }

  proc enc(m : ptxt) : rndness * ctxt = {
    var r, c;

    r <$ drndness;
    c <@ E.enc(k, r, m);
    return (r, c);
  }
}. 

(** The type of encryption oracles **)
module type CPA_Oracle_IV = {
  include CPA_Oracle_IV_i [enc]
}.

module type CPA_Distinguisher_IV (O : CPA_Oracle_IV) = {
  proc distinguish() : bool
}.

module Exp_IV_CPA (D : CPA_Distinguisher_IV) (O : CPA_Oracle_IV_i) = {
  proc run() = {
    var b;

         O.init();
    b <@ D(O).distinguish();
    return b;
  }
}.

module Counting_O (O : CPA_Oracle_IV_i) : CPA_Oracle_IV_i = {
  var counter : int 
  var log : rndness list

  proc init() : unit = {
    O.init();
    Counting_O.log <- [];
  }

  proc enc(m : ptxt) : rndness * ctxt = {
    var rc;

    counter <- counter + 1;
      
    rc <@ O.enc(m);
    log <- rc.`1 :: log;
      
    return rc;
  }
}.

(*
module (Counting_D (D : CPA_Distinguisher_IV) : CPA_Distinguisher_IV) (O : CPA_Oracle_IV) = {
  var counter : int
    
  module O_Counting : CPA_Oracle_IV = {
    proc enc(m : ptxt) : rndness * ctxt = {
      var rc;
      
      counter <- counter + 1;
      
      rc <@ O.enc(m);
      
      return rc;
    }
  }

  proc distinguish() = {
    var b : bool;
    
    b <@ D(O_Counting).distinguish();
    
    return b;
  }
}.*)

module (Reduction (D : CPA_Distinguisher_IV) : Adv_IND_NRCPA) (O: NRCPA_Oracle) = {
  module IV_Oracle : CPA_Oracle_IV = {
    var log : rndness list
    
    proc enc(m : ptxt) : rndness * ctxt = {
      var r : rndness;
      var c : ctxt option;

      r <$ drndness;
      log <- r :: log;
      
      c <@ O.enc(r, m);
        
      return (r, oget c);
    }
  }
    
  proc distinguish() : bool = {
    var b : bool;

    IV_Oracle.log <- [];
    
    b <@ D(IV_Oracle).distinguish();
    
    return b /\ uniq IV_Oracle.log;
  }
}.

(** Proof for security of IV-based encryption **)
section.

declare module D <: CPA_Distinguisher_IV{ -O_NRCPA_real, -O_NRCPA_ideal, -O_IV_real, -O_IV_ideal, -O_NRPRF_ideal, -O_NRPRF_real, -Reduction, -Counting_O }.

lemma Counting_real &m:
  Pr[Exp_IV_CPA(D, O_IV_real(E)).run() @ &m: res] =
  Pr[Exp_IV_CPA(D, Counting_O(O_IV_real(E))).run() @ &m: res].
proof.
byequiv (: ={glob D} ==> ={res})=> //.
proc; inline *.
call (: ={O_IV_real.k}).
+ by proc; inline *; auto.
by auto.
qed.

lemma Counting_ideal &m:
  Pr[Exp_IV_CPA(D, O_IV_ideal).run() @ &m: res] =
  Pr[Exp_IV_CPA(D, Counting_O(O_IV_ideal)).run() @ &m: res].
proof.
byequiv => //; proc; inline *. sp.
call (: true).
proc. inline *. auto. skip => //=.
qed.

declare axiom D_ll (O <: CPA_Oracle_IV {-D}): islossless O.enc => islossless D(O).distinguish.

(** maximal number of queries to the encryption oracle **)
declare op q : { int | 0 <= q } as ge0_q.

local clone import Birthday as BB with 
  op q <- q,
  type T <- rndness,
  op uT <- drndness
proof *. 
realize ge0_q by exact: ge0_q.
(*realize maxuP. by move=> x; rewrite (drndness_uni x maxu) 1,2:drndness_fu. qed.  (* change that in birthday theory! *)*)

declare axiom D_bounded (O <: CPA_Oracle_IV_i {-D}) : 
  hoare[D(Counting_O(O)).distinguish : Counting_O.counter = 0 ==> Counting_O.counter <= q].

local lemma Counting_bounded_real :
  hoare[Exp_IV_CPA(D, Counting_O(O_IV_real(E))).run : Counting_O.counter = 0 ==> Counting_O.counter <= q].
proof. proc; inline *. seq 3 : #pre. auto. call (D_bounded (O_IV_real(E))) => //=. qed.

local lemma Counting_bounded_ideal :
  hoare[Exp_IV_CPA(D, Counting_O(O_IV_ideal)).run : Counting_O.counter = 0 ==> Counting_O.counter <= q].
proof.  proc; inline *. call (D_bounded (O_IV_ideal)) => //=. auto. qed.

local module O_IV_S_real (S: Sampler) (E: Enc_Scheme) : CPA_Oracle_IV_i = {
  var k : key
  
  proc init() : unit = {
    k <@ E.kgen();
    S.init();
  }
  
  proc enc(m : ptxt) : rndness * ctxt = {
    var r : rndness;
    var c : ctxt;
    
    r <@ S.s();
    c <@ E.enc(O_IV_S_real.k, r, m);
    
    return (r, c);
  }
}.

local module O_IV_S_ideal (S: Sampler) : CPA_Oracle_IV_i = {
  var k : key
  
  proc init() : unit = {
    S.init();
  }
  
  proc enc(m : ptxt) : rndness * ctxt = {
    var r : rndness;
    var c : ctxt;
    
    r <@ S.s();
    c <$ dctxt;
    
    return (r, c);
  }
}.

local lemma Sample_real &m:
  Pr[Exp_IV_CPA(D, O_IV_real(E)).run() @ &m: res] =
  Pr[Exp_IV_CPA(D, O_IV_S_real(Sample, E)).run() @ &m: res].
proof.
byequiv => //. 
proc; inline *.
sim (: ={k}(O_IV_real, O_IV_S_real)).
proc; inline *. 
by wp; rnd; skip.
qed.

local lemma Sample_ideal &m:
  Pr[Exp_IV_CPA(D, O_IV_ideal).run() @ &m: res] =
  Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m: res].
proof.
byequiv => //. 
proc; inline *.
call(: true).
+ proc; inline *.
  by wp; rnd; wp; rnd; skip. 
by wp.
qed.

local lemma IV_S_real_uniq &m: 
  Pr[Exp_IV_CPA(D, O_IV_S_real(Sample, E)).run() @ &m: res /\ uniq Sample.l]
  = 
  Pr[Exp_IND_NRCPA(O_NRCPA_real(E), Reduction(D)).run() @ &m: res].
proof.
byequiv => //.
proc; inline *. 
wp.
call (: ! uniq Reduction.IV_Oracle.log, 
           ={k}(O_IV_S_real, O_NRCPA_real)
        /\ Sample.l{1} = Reduction.IV_Oracle.log{2}
        /\ Reduction.IV_Oracle.log{2} = O_NRCPA_real.log{2},
        uniq Sample.l{1} = uniq Reduction.IV_Oracle.log{2}) => //=.
+ apply D_ll.
+ proc; inline *. 
  seq 2 2 : (   ={m}
             /\ r0{1} = r{2}
             /\ O_IV_S_real.k{1} = O_NRCPA_real.k{2} 
             /\ Sample.l{1} = Reduction.IV_Oracle.log{2}
             /\ Reduction.IV_Oracle.log{2} = r{2} :: O_NRCPA_real.log{2}). 
  - wp. rnd. skip => //.
  case (uniq Reduction.IV_Oracle.log{2}); last first.
  - conseq (: _ ==> true) => />.
    by wp.
  rcondt{2} 3; 1: by move=> ?; wp; skip.
  by wp; skip.
+ move=> &2 uql.
  proc; inline *.
  wp; rnd; skip => />.
  rewrite uql => &1 -> /=.
  by rewrite drndness_ll.
+ move=> &1.
  proc; inline *.
  wp; rnd; skip => />.
  by rewrite drndness_ll.
by wp; rnd; skip => /> /#.
qed.

local lemma IV_S_ideal_uniq &m: 
  Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m: res /\ uniq Sample.l]
  = 
  Pr[Exp_IND_NRCPA(O_NRCPA_ideal, Reduction(D)).run() @ &m: res].
proof.
byequiv => //.
proc; inline *. 
wp.
call (: ! uniq Reduction.IV_Oracle.log,
           Sample.l{1} = Reduction.IV_Oracle.log{2}
        /\ Reduction.IV_Oracle.log{2} = O_NRCPA_ideal.log{2},
        uniq Sample.l{1} = uniq Reduction.IV_Oracle.log{2}) => //=.
+ apply D_ll.
+ proc; inline *. 
  seq 2 2 : (   ={m}
             /\ r0{1} = r{2} 
             /\ Sample.l{1} = Reduction.IV_Oracle.log{2}
             /\ Reduction.IV_Oracle.log{2} = r{2} :: O_NRCPA_ideal.log{2}). 
  - by wp; rnd; skip.
  case (uniq Reduction.IV_Oracle.log{2}); last first.
  - conseq (: _ ==> true) => />.
    wp; sp.
    if{2} => /=.
    * by wp; rnd; wp; skip.
    by rnd{1}; wp; skip.
  rcondt{2} 3; 1: by move=> ?; wp; skip.
  by wp; rnd; wp; skip.
+ move=> &2 uql.
  proc; inline *.
  rnd; wp; rnd; skip => />.
  rewrite uql => &1 -> /=.
  by rewrite dptxt_ll drndness_ll.
+ move=> &1.
  proc; inline *.
  wp. 
  seq 1 : #pre => //. 
  - by rnd; skip; rewrite drndness_ll.
  - sp; if.
    * wp; rnd; wp; skip.
      by rewrite dptxt_ll /#.
    by wp; skip => />.
  hoare => /=.
  by rnd; skip. 
by wp; skip => /> /#.
qed.

local module S' (S : ASampler) = {
  include S
  
  proc init() = {}
}.
  
local module (BB_Reduction_real (E : Enc_Scheme) : Adv) (S : ASampler) = {
  proc a() = {
    O_IV_S_real(S'(S), E).init();
    
    D(O_IV_S_real(S'(S), E)).distinguish();
  }
}.

local module (BB_Reduction_ideal : Adv) (S : ASampler) = {
  proc a() = {
    O_IV_S_ideal(S'(S)).init();
    
    D(O_IV_S_ideal(S'(S))).distinguish();
  }
}.

local equiv blop:
    D(O_IV_S_real(S'(Sample), E)).distinguish
  ~ D(Counting_O(O_IV_S_real(S'(Sample), E))).distinguish:
  ={glob D, O_IV_S_real.k, Sample.l} /\ (size Sample.l = Counting_O.counter){2}
  ==> ={res, O_IV_S_real.k, Sample.l} /\ (size Sample.l = Counting_O.counter){2}.
proof.
proc (={O_IV_S_real.k, Sample.l} /\ (size Sample.l = Counting_O.counter){2})=> //.
by proc; inline *; auto=> /> &2 _ _; rewrite addzC.
qed.

local equiv blopii:
    D(O_IV_S_ideal(S'(Sample))).distinguish
  ~ D(Counting_O(O_IV_S_ideal(S'(Sample)))).distinguish:
  ={glob D, O_IV_S_ideal.k, Sample.l} /\ (size Sample.l = Counting_O.counter){2}
  ==> ={res, O_IV_S_ideal.k, Sample.l} /\ (size Sample.l = Counting_O.counter){2}.
proof.
proc (={O_IV_S_ideal.k, Sample.l} /\ (size Sample.l = Counting_O.counter){2})=> //.
by proc; inline *; auto=> /> &2 _ _; rewrite addzC.
qed.

local lemma Counting_BB_Reduction_real :
  hoare[BB_Reduction_real(E, Sample).a : size Sample.l = 0 ==> size Sample.l <= q].
proof.
proc; inline *; seq 2 : #pre; auto.
call (: size Sample.l = 0 ==> size Sample.l <= q)=> //.
conseq blop (: Counting_O.counter = 0 ==> Counting_O.counter <= q)=> />.
+ move=> &1 size_0; exists (glob D){1} 0 O_IV_S_real.k{1} Sample.l{1}=> />.
by conseq (D_bounded (O_IV_S_real(S'(Sample), E))).
qed.

local lemma Counting_BB_Reduction_ideal :
  hoare[BB_Reduction_ideal(Sample).a : size Sample.l = 0 ==> size Sample.l <= q].
proof.
proc; inline *.
call (: size Sample.l = 0 ==> size Sample.l <= q)=> //.
conseq blopii (: Counting_O.counter = 0 ==> Counting_O.counter <= q)=> />.
+ move=> &1 size_0; exists (glob D){1} 0 O_IV_S_ideal.k{1} Sample.l{1}=> />.
by conseq (D_bounded (O_IV_S_ideal(S'(Sample)))).
qed.

local lemma help1 &m:
  Pr[Exp_IV_CPA(D, O_IV_S_real(Sample, E)).run() @ &m : ! uniq Sample.l] =
  Pr[Exp(Sample, BB_Reduction_real(E)).main() @ &m : ! uniq Sample.l].
proof.
byequiv (: _ ==> ={Sample.l}) => //=.
proc; inline *.  
call (: ={O_IV_S_real.k, Sample.l}) => //.
* proc; inline *.      
  by wp; rnd; skip.
by wp; rnd; wp; skip.
qed.

local lemma help2 &m:
  Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m : ! uniq Sample.l] =
  Pr[Exp(Sample, BB_Reduction_ideal).main() @ &m : ! uniq Sample.l].
proof.
byequiv (: _ ==> ={Sample.l}) => //=.
proc; inline *.  
call (: ={Sample.l}) => //.
- proc; inline *.      
  by rnd; wp; rnd; skip.
by wp; skip.
qed.


lemma IV_security_NR &m:
  `| Pr[Exp_IV_CPA(D, O_IV_real(E)).run() @ &m: res]
     - Pr[Exp_IV_CPA(D, O_IV_ideal).run() @ &m: res] |
  <= 
  `| Pr[Exp_IND_NRCPA(O_NRCPA_real(E), Reduction(D)).run() @ &m: res]
     - Pr[Exp_IND_NRCPA(O_NRCPA_ideal, Reduction(D)).run() @ &m: res] | 
   + (q * (q - 1))%r / 2%r * mu1 drndness witness.
proof.
rewrite Sample_real Sample_ideal Pr[mu_split (uniq Sample.l)].
have ->:
  Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m : res]
  =
  Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m : res /\ uniq Sample.l] +
  Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m : res /\ ! uniq Sample.l]. 
+ by rewrite Pr[mu_split uniq Sample.l].
rewrite StdOrder.RealOrder.Domain.opprD -StdOrder.RealOrder.Domain.addrCA.
apply (StdOrder.RealOrder.ler_trans 
        (`| Pr[Exp_IV_CPA(D, O_IV_S_real(Sample, E)).run() @ &m : res /\ uniq Sample.l] -
            Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m : res /\ uniq Sample.l] | +
         `| Pr[Exp_IV_CPA(D, O_IV_S_real(Sample, E)).run() @ &m : res /\ ! uniq Sample.l] -
            Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m : res /\ ! uniq Sample.l] |)).
+ smt(StdOrder.RealOrder.ler_norm_add).
rewrite StdOrder.RealOrder.ler_add 1:StdOrder.RealOrder.ler_eqVlt.
+ by rewrite IV_S_real_uniq IV_S_ideal_uniq.
apply (StdOrder.RealOrder.ler_trans
        (StdOrder.RealOrder.maxr 
            Pr[Exp_IV_CPA(D, O_IV_S_real(Sample, E)).run() @ &m : res /\ ! uniq Sample.l]
            Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m : res /\ ! uniq Sample.l])).
+ by rewrite StdOrder.RealOrder.ler_norm_maxr Pr[mu_ge0].
rewrite StdOrder.RealOrder.maxrE (: mu1 drndness witness = mu1 drndness maxu).
+ by rewrite (drndness_uni witness maxu) 1,2:drndness_fu.
case (Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m : res /\ ! uniq Sample.l] <=
      Pr[Exp_IV_CPA(D, O_IV_S_real(Sample, E)).run() @ &m : res /\ ! uniq Sample.l]) => ?.
+ apply (StdOrder.RealOrder.ler_trans 
          (Pr[Exp_IV_CPA(D, O_IV_S_real(Sample, E)).run() @ &m : ! uniq Sample.l])).
  - byequiv (: ={glob D} ==> ={Sample.l}) => //.
    proc; inline *.
    call (: ={O_IV_S_real.k, Sample.l}).
    * proc; inline *.
      by wp; rnd; skip.
    by wp; rnd; skip.
  rewrite help1.
  apply (pr_collision (BB_Reduction_real(E))); 1: move=> T Tll. 
  - proc; inline *.
    call (: true); 1: by apply D_ll.
    * proc; inline *.
      by wp; call(: true).
    by wp; rnd; skip; rewrite dkey_ll.
    by apply Counting_BB_Reduction_real.
apply (StdOrder.RealOrder.ler_trans 
          (Pr[Exp_IV_CPA(D, O_IV_S_ideal(Sample)).run() @ &m : ! uniq Sample.l])).
+ byequiv (: ={glob D} ==> ={Sample.l}) => //.
  proc; inline *.
  call (: ={Sample.l}).
  - proc; inline *.
    by rnd; wp; rnd; skip.
  by wp; skip.
rewrite help2.
apply (pr_collision (BB_Reduction_ideal)); 1: move=> T Tll. 
+ proc; inline *.
  call (: true) => //; 1: by apply D_ll.
  proc; inline *.
  by rnd; call(: true); skip; rewrite dptxt_ll.
by apply Counting_BB_Reduction_ideal.
qed.

lemma IV_security_PRF &m:
  `| Pr[Exp_IV_CPA(D, O_IV_real(E)).run() @ &m: res]
     - Pr[Exp_IV_CPA(D, O_IV_ideal).run() @ &m: res] |
  <= 
  `| Pr[Exp_NRPRF(O_NRPRF_real, R_NRPRF_IND_NRCPA(Reduction(D))).run() @ &m: res]
     - Pr[Exp_NRPRF(O_NRPRF_ideal, R_NRPRF_IND_NRCPA(Reduction(D))).run() @ &m: res] |
   + (q * (q - 1))%r / 2%r * mu1 drndness witness.
proof. 
apply (StdOrder.RealOrder.ler_trans
          (`| Pr[Exp_IND_NRCPA(O_NRCPA_real(E), Reduction(D)).run() @ &m: res]
              - Pr[Exp_IND_NRCPA(O_NRCPA_ideal, Reduction(D)).run() @ &m: res] | 
            + (q * (q - 1))%r / 2%r * mu1 drndness witness)).
+ by apply IV_security_NR.
by rewrite (EqAdvantage_IND_NRCPA_NRPRF (Reduction(D))).
qed.

end section.
