(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List FSet Finite Distr OldMonoid.
require import Indist.
require (*--*) CHoareTactic.
(*---*) import StdBigop.Bigint BIA.

type pkey.
type skey.
type plaintext.
type ciphertext.

module type Scheme = {
  proc kg() : pkey * skey
  proc enc(pk:pkey, m:plaintext)  : ciphertext
  proc dec(sk:skey, c:ciphertext) : plaintext option
}.

module Correctness (S:Scheme) = {
  proc main(m:plaintext) : bool = {
    var pk : pkey;
    var sk : skey;
    var c  : ciphertext;
    var m' : plaintext option;

    (pk, sk) <@ S.kg();
    c        <@ S.enc(pk, m);
    m'       <@ S.dec(sk, c);
    return (m' = Some m);
  }
}.

module type LR = {
  proc orcl (m0 m1:plaintext) : ciphertext
}.

module type AdvCPA (S)(LR:LR) = {
  proc main(pk:pkey) : bool
}.

module K = {
  var pk : pkey
  var sk : skey
  var b  : bool
}.

module L (S:Scheme) = {

  proc orcl (m0 m1:plaintext) : ciphertext = {
    var r : ciphertext;
    r   <@ S.enc(K.pk,m0);
    return r;
  }
}.

module R (S:Scheme) = {

  proc orcl (m0 m1:plaintext) : ciphertext = {
    var r : ciphertext;
    r   <@ S.enc(K.pk,m1);
    return r;
  }
}.

module LRb (S:Scheme) = {

  proc orcl (m0 m1:plaintext) : ciphertext = {
    var r : ciphertext;
    r   <@ S.enc(K.pk,K.b?m0:m1);
    return r;
  }
}.

module CPAL (S:Scheme,A: fun (LR{+L(S)) => sig include AdvCPA(LR) end) = {
  module A = A(L(S))
  proc main():bool = {
    var b':bool;
    (K.pk,K.sk) <@ S.kg();
    b'          <@ A.main(K.pk);
    return b';
  }
}.

module CPAR (S:Scheme,A:AdvCPA) = {
  module A = A(R(S))
  proc main():bool = {
    var b':bool;
    (K.pk,K.sk) <@ S.kg();
    b'          <@ A.main(K.pk);
    return b';
  }
}.

module CPA (S:Scheme,A:AdvCPA) = {
  module LRb = {
    var b : bool
  }
  module A = A(LRb(S))
  proc main():bool = {
    var b':bool;
    K.b         <$ {0,1};
    (K.pk,K.sk) <@ S.kg();
    b'          <@ A.main(K.pk);
    return b';
  }
}.

clone import Indist as Ind with
  type input <- plaintext,
  type H.output <- ciphertext,
  type H.inleaks <- unit,
  type H.outleaks <- pkey. 

module ToOrcl (S:Scheme) = {
  proc leaks (il:unit) : pkey = {
    (K.pk, K.sk) <@ S.kg();
    return K.pk;
  }
  proc orcl (m:plaintext) : ciphertext = {
    var c : ciphertext;
    c <@ S.enc(K.pk, m);
    return c;
  }
}.

module ToAdv(A:AdvCPA, O:Orcl,LR:LR) = {
  proc main() : bool = {
    var pk:pkey;
    var b':bool;
    pk <@ O.leaks();
    b' <@ A(LR).main(pk);
    return b';
  }
}.

module B (S:Scheme, A:AdvCPA, LR:LR) = {
  module A = A(HybOrcl2(ToOrcl(S),LR))
  proc main(pk:pkey) : bool = {
    var b':bool;
    H.HybOrcl.l0 <$ [0..H.q-1];
    H.HybOrcl.l <- 0;
    b' <@ A.main(pk);
    return b';
  }
}.

(* Complexity of the adversary *)
op cA : { int | 0 <= cA } as cA_pos.

type cScheme = {
  ckg  : int;
  cenc : int;
  cdec : int;
}.

(* Complexity of the scheme *)
op cs : cScheme.
axiom cs_pos : 0 <= cs.`ckg /\ 0 <= cs.`cenc /\ 0 <= cs.`cdec.

op cincr : int -> int.
schema cost_incr {n:int} (m:int) : cost[`|n| <= m : n + 1] = cost[true:n] + cincr m.
hint simplify cost_incr.

op cltint : int -> int.
schema cost_ltint {n1 n2:int} (m:int) : cost[`|n1| <= m /\ `|n2| <= m : n1 < n2] = cost[true:n1] + cost[true:n2] + cltint m.
hint simplify cost_ltint.

op ceqint : int -> int.
schema cost_eqint {n1 n2:int} (m:int) : cost[`|n1| <= m /\ `|n2| <= m : n1 = n2] = cost[true:n1] + cost[true:n2] + ceqint m.
hint simplify cost_eqint.

schema cost_ltint_P `{P} {n1 n2:int} (m:int) : cost[P /\ `|n1| <= m /\ `|n2| <= m : n1 < n2] = cost[P:n1] + cost[P:n2] + cltint m.
hint simplify cost_ltint_P.

schema cost_eqint_P `{P} {n1 n2:int} (m:int) : cost[P /\ `|n1| <= m /\ `|n2| <= m : n1 = n2] = cost[P:n1] + cost[P:n2] + ceqint m.
hint simplify cost_eqint_P.

op cdinterval : int -> int.
schema cost_dinterval {i j : int} (k:int) : cost [ i <= j <= k - i : [i .. j - 1]] = cost [true : i] + cost [true : j] + cdinterval k.
hint simplify cost_dinterval.

axiom ge0_cincr m : 0 <= cincr m.
axiom ge0_cltint m : 0 <= cltint m.
axiom ge0_ceqint m : 0 <= ceqint m.
axiom ge0_cdinterval m : 0 <= cdinterval m.

(* FIXME : does it make sense ? *)
schema cost_Hq `{P} : cost [P : H.q] = 0.
hint simplify cost_Hq.

section.

  declare module S:Scheme [ kg : `{cs.`ckg},
                            enc: `{cs.`cenc}]
                 {-K, -H.Count, -H.HybOrcl}.
    (* Normaly I would like to locally
       clone Indist in the section, in that case
       restrictions at least on H.c are not needed.
       But LRB and B are used so we need to do it
     *)
  
  declare module A:AdvCPA [main : `{cA, #LR.orcl: H.q}] {-K,-H.Count,-H.HybOrcl,-S}.

  axiom La   : forall (LR<:LR{-A}), islossless LR.orcl => islossless A(LR).main.

  local lemma cost_AL : 
     choare [A(OrclL(ToOrcl(S))).main : H.Count.c = 0 ==> H.Count.c <= H.q] 
     time [cincr H.q * H.q;
           A.main : 1;
           S.enc  : H.q].
  proof.
    proc true :
         (OrclL(ToOrcl(S)).orcl : H.Count.c) time
         [ (OrclL(ToOrcl(S)).orcl : [fun _ => cincr H.q; S.enc : fun _ => 1]) ] => //.
    + by move => />; rewrite !bigi_constz 1..2:[smt (H.q_pos)].
    move=> zo hzo; proc; inline *; wp := (`|H.Count.c| <= H.q); call (: true); auto => &hr /> /#.
  qed.

  local lemma AL_bound : hoare [A(OrclL(ToOrcl(S))).main : H.Count.c = 0 ==> H.Count.c <= H.q].
  proof. by conseq cost_AL. qed.

  local lemma cost_AR : 
     choare [A(OrclR(ToOrcl(S))).main : H.Count.c = 0 ==> H.Count.c <= H.q] 
     time [cincr H.q * H.q;
           A.main : 1;
           S.enc  : H.q].
  proof.
    proc true :
         (OrclR(ToOrcl(S)).orcl : H.Count.c) time
         [ (OrclR(ToOrcl(S)).orcl : [fun _ => cincr H.q; S.enc : fun _ => 1]) ] => //.
    + by move => />; rewrite !bigi_constz 1..2:[smt (H.q_pos)].
    move=> zo hzo; proc; inline *; wp; call(:true); wp:=(`|H.Count.c| <= H.q); skip => &hr /> /#.
  qed.

  local lemma AR_bound : hoare [A(OrclR(ToOrcl(S))).main : H.Count.c = 0 ==> H.Count.c <= H.q].
  proof. by conseq cost_AR. qed.

  local lemma cost_AHL : 
     choare [A(HybOrcl2(ToOrcl(S), OrclL(ToOrcl(S)))).main : 
         0 <= H.HybOrcl.l0 <= H.q /\ H.HybOrcl.l = 0 /\ H.Count.c = 0 ==> 
         H.HybOrcl.l <= H.q /\ H.Count.c <= 1 ]
      time [(cincr H.q + cincr 1 + cltint H.q + ceqint H.q) * H.q; S.enc : H.q; A.main : 1].
  proof.
    proc 
      (0 <= H.HybOrcl.l /\ 0 <= H.HybOrcl.l0 <= H.q /\ H.Count.c = if H.HybOrcl.l <= H.HybOrcl.l0 then 0 else 1):
      (HybOrcl2(ToOrcl(S), OrclL(ToOrcl(S))).orcl :  H.HybOrcl.l) time
      [ (HybOrcl2(ToOrcl(S), OrclL(ToOrcl(S))).orcl : [fun _ => cincr H.q + cincr 1 + cltint H.q + ceqint H.q; S.enc : fun _ => 1]) ] => //=.
    + by rewrite !bigi_constz 1,2:[smt(H.q_pos)].
    + by move=> &hr /> ->.
    + by move=> /> /#.
    move=> zo hzo; proc; inline *.
    wp := (`|H.HybOrcl.l| <= H.q).
    if := (`| H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q); 1: smt().
    + by wp; call (:true; time []); auto => &hr />; smt (ge0_cincr ge0_cltint ge0_ceqint).
    if := (`| H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q); 1: smt().
    + wp := (`|H.Count.c| <= 1); call (:true; time []); auto => &hr />.
      smt (ge0_cincr ge0_cltint ge0_ceqint).
    by wp; call (:true; time []); auto => &hr />; smt (ge0_cincr ge0_cltint ge0_ceqint).
  qed.

  local lemma AHL_bound :  
     hoare [A(HybOrcl2(ToOrcl(S), OrclL(ToOrcl(S)))).main : 
         0 <= H.HybOrcl.l0 <= H.q /\ H.HybOrcl.l = 0 /\ H.Count.c = 0 ==> 
         H.HybOrcl.l <= H.q /\ H.Count.c <= 1 ].
  proof. by conseq cost_AHL. qed.

  local lemma cost_AHR : 
     choare [A(HybOrcl2(ToOrcl(S), OrclR(ToOrcl(S)))).main : 
         0 <= H.HybOrcl.l0 <= H.q /\ H.HybOrcl.l = 0 /\ H.Count.c = 0 ==> 
         H.HybOrcl.l <= H.q /\ H.Count.c <= 1 ]
      time [(cincr H.q + cincr 1 + cltint H.q + ceqint H.q) * H.q; S.enc : H.q; A.main : 1].
  proof.
    proc 
      (0 <= H.HybOrcl.l /\ 0 <= H.HybOrcl.l0 <= H.q /\ H.Count.c = if H.HybOrcl.l <= H.HybOrcl.l0 then 0 else 1):
      (HybOrcl2(ToOrcl(S), OrclR(ToOrcl(S))).orcl :  H.HybOrcl.l) time
      [ (HybOrcl2(ToOrcl(S), OrclR(ToOrcl(S))).orcl : [fun _ => cincr H.q + cincr 1 + cltint H.q + ceqint H.q; S.enc : fun _ => 1]) ] => //=.
    + by rewrite !bigi_constz 1,2:[smt(H.q_pos)].
    + by move=> &hr /> ->.
    + by move=> /> /#.
    move=> zo hzo; proc; inline *.
    wp := (`|H.HybOrcl.l| <= H.q).
    if := (`| H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q); 1: smt().
    + by wp; call (:true; time []); auto => &hr />; smt (ge0_cincr ge0_cltint ge0_ceqint).
    if := (`| H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q); 1: smt().
    + wp; call (:true; time []); wp := (`|H.Count.c| <= 1); skip => &hr />.
      smt (ge0_cincr ge0_cltint ge0_ceqint).
    by wp; call (:true; time []); auto => &hr />; smt (ge0_cincr ge0_cltint ge0_ceqint).
  qed.

  local lemma AHR_bound :  
     hoare [A(HybOrcl2(ToOrcl(S), OrclR(ToOrcl(S)))).main : 
         0 <= H.HybOrcl.l0 <= H.q /\ H.HybOrcl.l = 0 /\ H.Count.c = 0 ==> 
         H.HybOrcl.l <= H.q /\ H.Count.c <= 1 ].
  proof. by conseq cost_AHR. qed.
 
  lemma CPA1_CPAn &m :
    Pr[CPAL(S,B(S,A)).main() @ &m : res] -
    Pr[CPAR(S,B(S,A)).main() @ &m : res] =
    1%r/H.q%r * (Pr[CPAL(S,A).main() @ &m : res] - Pr[CPAR(S,A).main() @ &m : res]).
  proof.
    cut -> : Pr[CPAL(S, A).main() @ &m : res] =
             Pr[INDL(ToOrcl(S),ToAdv(A)).main() @ &m : res].
      byequiv (_ : ={glob A, glob S} ==>
                        ={res,glob A, glob S, K.pk}) => //.
      proc.
      inline INDL(ToOrcl(S), ToAdv(A)).A.main H.Count.init  ToOrcl(S).leaks.
      wp;call (_: ={glob S, K.pk}).
        by proc;inline ToOrcl(S).orcl H.Count.incr;wp;call (_:true);wp.
      by wp;call (_:true);wp.
    cut -> : Pr[CPAR(S, A).main() @ &m : res] =
             Pr[INDR(ToOrcl(S),ToAdv(A)).main() @ &m : res].
      byequiv (_ : ={glob A, glob S} ==>
                        ={res,glob A, glob S, K.pk}) => //.
      proc.
      inline INDR(ToOrcl(S), ToAdv(A)).A.main H.Count.init  ToOrcl(S).leaks.
      wp;call (_: ={glob S, K.pk}).
        by proc;inline ToOrcl(S).orcl H.Count.incr;wp;call (_:true);wp.
      by wp;call (_:true);wp.
    cut := IND1_INDn (ToOrcl(S)) (ToAdv(A)) _ _ _ H.q_pos &m (fun ga go c, true) => //=.
    + have h : choare [ToOrcl(S).leaks : true ==> true] time [0; S.kg:1].
      + by proc; call (_:true); skip.
      conseq h.
    + have h : choare [ToOrcl(S).orcl : true ==> true] time [0; S.enc:1].
      + by proc; call (_:true); skip.
      conseq h.
      move=> O LR Llr Ll Lo;proc;call (La LR _) => //.
      by call Ll.
    have -> : Pr[INDL(ToOrcl(S), ToAdv(A)).main() @ &m : res /\ H.Count.c <= H.q] =
              Pr[INDL(ToOrcl(S), ToAdv(A)).main() @ &m : res].
    + byequiv => //.
      conseq (_: ={glob A,glob S} ==> ={res}) (_: true ==> H.Count.c <= H.q) => //; last by sim.
      proc; inline *; wp. by call AL_bound; wp; call (:true); wp.
    have -> : Pr[INDR(ToOrcl(S), ToAdv(A)).main() @ &m : res /\ H.Count.c <= H.q] =
              Pr[INDR(ToOrcl(S), ToAdv(A)).main() @ &m : res].
    + byequiv => //.
      conseq (_: ={glob A,glob S} ==> ={res}) (_: true ==> H.Count.c <= H.q) => //; last by sim.
      by proc; inline *; wp; call AR_bound; wp; call(:true); auto.
    move=> <-; congr; last congr.
    + have -> : Pr[INDL(ToOrcl(S), HybGame2(ToAdv(A))).main() @ &m : res /\ H.HybOrcl.l <= H.q /\ H.Count.c <= 1] =
                Pr[INDL(ToOrcl(S), HybGame2(ToAdv(A))).main() @ &m : res ].
      + byequiv => //.
        conseq (_: ={glob A,glob S} ==> ={res}) (_: true ==>  H.HybOrcl.l <= H.q /\ H.Count.c <= 1) => //; last by sim.
        proc; inline *; wp; call AHL_bound; auto; call(:true); auto.
        smt (DInterval.supp_dinter).
      byequiv (_: ={glob S,glob A} ==> ={res,glob H.HybOrcl}) => //.
      proc.
      inline INDL(ToOrcl(S), Ind.HybGame2(ToAdv(A))).A.main H.Count.init CPAL(S, B(S,A)).A.main
        Ind.HybGame2(ToAdv(A), ToOrcl(S), OrclL(ToOrcl(S))).A.main.
      wp.
      call (_: ={glob S,glob H.HybOrcl, K.pk}).
        proc;wp.
        if => //.
          by call (_: ={glob S, K.pk});first sim.
        if => //.
          call (_: ={glob S, K.pk}) => //.
          by inline ToOrcl(S).orcl H.Count.incr;wp;call (_: true);wp.
        by call (_: ={glob S, K.pk});first sim.
      swap{1} [3..4] -2;inline ToOrcl(S).leaks;wp.
      by call (_:true);wp;rnd;wp.
    have -> : Pr[INDR(ToOrcl(S), HybGame2(ToAdv(A))).main() @ &m : res /\ H.HybOrcl.l <= H.q /\ H.Count.c <= 1] =
              Pr[INDR(ToOrcl(S), HybGame2(ToAdv(A))).main() @ &m : res].
    + byequiv => //.
      conseq (_: ={glob A,glob S} ==> ={res}) (_: true ==>  H.HybOrcl.l <= H.q /\ H.Count.c <= 1) => //; last by sim.
      proc; inline *; wp; call AHR_bound; auto; call(:true); auto.
      smt (DInterval.supp_dinter).
    byequiv (_: ={glob S,glob A} ==> ={res,glob H.HybOrcl}) => //.
    proc.
    inline INDR(ToOrcl(S), Ind.HybGame2(ToAdv(A))).A.main H.Count.init CPAR(S, B(S,A)).A.main
      Ind.HybGame2(ToAdv(A), ToOrcl(S), OrclR(ToOrcl(S))).A.main.
    wp. 
    call (_: ={glob S,glob H.HybOrcl, K.pk}).
      proc;wp.
      if => //.
        by call (_: ={glob S, K.pk});first sim.
      if => //.
        call (_: ={glob S, K.pk}) => //.
        by inline ToOrcl(S).orcl H.Count.incr;wp;call (_: true);wp.
      by call (_: ={glob S, K.pk});first sim.
    swap{1} [3..4] -2;inline ToOrcl(S).leaks;wp.
    by call (_:true);wp;rnd;wp.
  qed.

  lemma big_b2i ['a] (P:'a -> bool) s : big predT (fun k => b2i (P k)) s = big P (fun _ => 1) s.
  proof. by rewrite (big_mkcond P); apply congr_big. qed.

  lemma bigi_b2i_split (k n m:int) P F:
    n <= k < m =>
    bigi P F n m = bigi P F n k + b2i (P k) * F k + bigi P F (k+1) m.
  proof.
    move=> h; rewrite (big_cat_int k n m) 1,2:/#.
    rewrite (big_ltn_cond k m) 1:/# /b2i; case: (P k) => *; ring.
  qed.

  lemma bigi_inP (n m:int) P F:
    (forall i, n <= i < m => P i) =>
    bigi P F n m = bigi predT F n m.
  proof. by move=> h; apply congr_big_int => // i /h ->. qed.

  lemma bigi1 (n m:int) P F:
    (forall i, n <= i < m => P i => F i = 0) =>
    bigi P F n m = 0.
  proof.
    by move=> h; apply big1_seq => i [] hP /mem_range hin; apply h.
  qed.


  lemma ex_CPA1_CPAn &m : 
    exists (B <: AdvCPA [main : `{ (cincr H.q + ceqint H.q + cltint H.q) * H.q + cdinterval H.q +
                                    (H.q - 1) * cs.`cenc + cA,
                                    #LR.orcl : 1}
                                 ]
                         {+A,+H.HybOrcl, +K, +S}),
      Pr[CPAL(S,A).main() @ &m : res] - Pr[CPAR(S,A).main() @ &m : res] =
      H.q%r * (Pr[CPAL(S,B).main() @ &m : res] - Pr[CPAR(S,B).main() @ &m : res]).
  proof.
    exists (B(S,A)); split; last by have -> := CPA1_CPAn &m; field; smt (H.q_pos).
    move=> clr MLR hclr.
    proc. 
    seq 2 : (H.HybOrcl.l =0 /\ 0 <= H.HybOrcl.l0 < H.q) time [ (cincr H.q + ceqint H.q + cltint H.q) * H.q;
                                                               S.enc : (H.q - 1);
                                                               A.main : 1;
                                                               MLR.orcl : 1].
    + wp; rnd (0 <= H.q <= H.q - 0); skip => &hr />.
      instantiate /(_ H.q) /= -> := (cost_dinterval {b' : bool, pk : pkey} 0 H.q).     
      smt (DInterval.supp_dinter DInterval.dinter_ll H.q_pos).
    exlim H.HybOrcl.l0 => l0. 
    call (_: (0 <= H.HybOrcl.l /\ 0 <= H.HybOrcl.l0 <= H.q /\ l0 = H.HybOrcl.l0); 
       (HybOrcl2(ToOrcl(S), MLR).orcl : H.HybOrcl.l) time
      [ (HybOrcl2(ToOrcl(S), MLR).orcl : [fun _ => cincr H.q + ceqint H.q + cltint H.q ; 
                                          S.enc : fun k => b2i (k <> l0); MLR.orcl : fun k => b2i(k=l0)]) ]) => //=.
    + move=> zo hzo; proc; inline *; wp := (`|H.HybOrcl.l| <= H.q).
      if := (`|H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q); 1: smt().
      + wp; call (:true; time []); auto => &hr />; smt (ge0_ceqint). 
      if := (`|H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q); 1: smt().
      + admit.
      by wp; call (:true; time []); auto => &hr /> /#. 
p : fun(x:M') => M
fun (x:M'') : fun(x:M'') => M => p(x) 

    skip => &hr />; move: (H.HybOrcl.l0{hr}) => {l0}l0 h0 hq .
    rewrite bigi_constz 1:[smt (H.q_pos)] /=.
    rewrite !big_b2i !(bigi_b2i_split l0 0 H.q) 1,2:// /b2i /=.
    rewrite !(bigi_inP _ _ (fun (k : int) => k <> l0)) 1,2:/# !bigi_constz 1:// 1:/#.
    by rewrite !bigi1 /= /#.
  qed.

  lemma ex_CPA1_CPAn &m : 
    exists (B <: AdvCPA {+A,+H.HybOrcl, +K, +S}),
      (forall (clr:int) (MLR<:LR [orcl: `{clr}] {-H.HybOrcl}), 
         
         choare[B(MLR).main : true ==> true] time
                  [ (cincr H.q + ceqint H.q + cltint H.q) * H.q + cdinterval H.q;
                    S.enc: (H.q - 1);
                    A.main : 1;
                    MLR.orcl : 1]) /\
      Pr[CPAL(S,A).main() @ &m : res] - Pr[CPAR(S,A).main() @ &m : res] =
      H.q%r * (Pr[CPAL(S,B).main() @ &m : res] - Pr[CPAR(S,B).main() @ &m : res]).
  proof.
    exists (B(S,A)); split; last by have -> := CPA1_CPAn &m; field; smt (H.q_pos).
    move=> clr MLR.
    proc. 
    seq 2 : (H.HybOrcl.l =0 /\ 0 <= H.HybOrcl.l0 < H.q) time [ (cincr H.q + ceqint H.q + cltint H.q) * H.q;
                                                               S.enc : (H.q - 1);
                                                               A.main : 1;
                                                               MLR.orcl : 1].
    + wp; rnd (0 <= H.q <= H.q - 0); skip => &hr />.
      instantiate /(_ H.q) /= -> := (cost_dinterval {b' : bool, pk : pkey} 0 H.q).     
      smt (DInterval.supp_dinter DInterval.dinter_ll H.q_pos).
    exlim H.HybOrcl.l0 => l0. 
    call (_: (0 <= H.HybOrcl.l /\ 0 <= H.HybOrcl.l0 <= H.q /\ l0 = H.HybOrcl.l0); 
       (HybOrcl2(ToOrcl(S), MLR).orcl : H.HybOrcl.l) time
      [ (HybOrcl2(ToOrcl(S), MLR).orcl : [fun _ => cincr H.q + ceqint H.q + cltint H.q ; 
                                          S.enc : fun k => b2i (k <> l0); MLR.orcl : fun k => b2i(k=l0)]) ]) => //=.
    + move=> zo hzo; proc; inline *; wp := (`|H.HybOrcl.l| <= H.q).
      if := (`|H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q); 1: smt().
      + by wp; call (:true; time []); auto => &hr />; smt (ge0_ceqint). 
      if := (`|H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q); 1: smt().
      + by wp; call(:true; time []); auto => &hr /> /#.
      by wp; call (:true; time []); auto => &hr /> /#. 
    skip => &hr />; move: (H.HybOrcl.l0{hr}) => {l0}l0 h0 hq .
    rewrite bigi_constz 1:[smt (H.q_pos)] /=.
    rewrite !big_b2i !(bigi_b2i_split l0 0 H.q) 1,2:// /b2i /=.
    rewrite !(bigi_inP _ _ (fun (k : int) => k <> l0)) 1,2:/# !bigi_constz 1:// 1:/#.
    by rewrite !bigi1 /= /#.
  qed.
   
end section.
