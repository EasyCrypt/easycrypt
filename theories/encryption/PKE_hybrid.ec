(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List FSet Finite Distr DInterval.
require import Indist.
require import CHoareTactic.
(*---*) import StdBigop.Bigint BIA Xint.


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

module type AdvCPA (LR:LR) = {
  proc main(pk:pkey) : bool
}.

(* ==================================================================== *)
module K = {
  var c  : int
  var pk : pkey
  var sk : skey
  var b  : bool
}.

module L (S:Scheme) = {
  proc orcl (m0 m1:plaintext) : ciphertext = {
    var r : ciphertext;
    r   <@ S.enc(K.pk,m0);
    K.c <- K.c + 1;
    return r;
  }
}.

module R (S:Scheme) = {
  proc orcl (m0 m1:plaintext) : ciphertext = {
    var r : ciphertext;
    r   <@ S.enc(K.pk,m1);
    K.c <- K.c + 1;
    return r;
  }
}.

module LRb (S:Scheme) = {
  proc orcl (m0 m1:plaintext) : ciphertext = {
    var r : ciphertext;
    r   <@ S.enc(K.pk,K.b?m0:m1);
    K.c <- K.c + 1;
    return r;
  }
}.

module CPAL (S:Scheme) (A:AdvCPA) = {
  module A = A(L(S))

  proc main():bool = {
    var b':bool;

    K.c         <- 0;
    (K.pk,K.sk) <@ S.kg();
    b'          <@ A.main(K.pk);
    return b';
  }
}.

module CPAR (S:Scheme) (A:AdvCPA) = {
  module A = A(R(S))

  proc main():bool = {
    var b':bool;
    K.c         <- 0;
    (K.pk,K.sk) <@ S.kg();
    b'          <@ A.main(K.pk);
    return b';
  }
}.

module CPA (S:Scheme) (A:AdvCPA) = {
  proc main():bool = {
    var b':bool;

    K.c         <- 0;
    K.b         <$ {0,1};
    (K.pk,K.sk) <@ S.kg();
    b'          <@ A(LRb(S)).main(K.pk);
    return b';
  }
}.

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

clone import Indist as Ind with
  type input <- plaintext,
  type H.output <- ciphertext,
  type H.inleaks <- unit,
  type H.outleaks <- pkey. 

module ToAdv(A:AdvCPA) (O:Orcl) (LR:LR) = {
  proc main() : bool = {
    var pk:pkey;
    var b':bool;

    pk <@ O.leaks();
    b' <@ A(LR).main(pk);
    return b';
  }
}.

module B (S:Scheme) (A:AdvCPA) (LR:LR) = {
  proc main(pk:pkey) : bool = {
    var b':bool;

    H.HybOrcl.l0 <$ [0..H.q-1];
    H.HybOrcl.l <- 0;
    b' <@ A(HybOrcl2(ToOrcl(S),LR)).main(pk);
    return b';
  }
}.

section.
declare module S <: Scheme {-K, -H.Count, -H.HybOrcl}.
  (* Normaly I would like to locally
     clone Indist in the section, in that case
     restrictions at least on H.c are not needed.
     But LRB and B are used so we need to do it
   *)

declare module A <: AdvCPA {-K,-H.Count,-H.HybOrcl,-S}.

declare axiom Lkg  : islossless S.kg.
declare axiom Lenc : islossless S.enc.
declare axiom La   : forall (LR<:LR{-A}), islossless LR.orcl => islossless A(LR).main.

lemma CPA1_CPAn &m :
    0 < H.q
  =>     Pr[CPAL(S,B(S,A)).main() @ &m : res /\ H.HybOrcl.l <= H.q /\ K.c <= 1]
       - Pr[CPAR(S,B(S,A)).main() @ &m : res /\ H.HybOrcl.l <= H.q /\ K.c <= 1]
     = 1%r/H.q%r * (  Pr[CPAL(S,A).main() @ &m : res /\ K.c <= H.q]
                    - Pr[CPAR(S,A).main() @ &m : res /\ K.c <= H.q]).
proof.
move=> Hq.
have ->:   Pr[CPAL(S, A).main() @ &m : res /\ K.c <= H.q]
         = Pr[INDL(ToOrcl(S),ToAdv(A)).main() @ &m : res /\ H.Count.c <= H.q].
+ byequiv (: ={glob A, glob S}
           ==> ={res,glob A, glob S, K.pk} /\ K.c{1} = H.Count.c{2})=> //.
  proc.
  inline ToAdv(A, ToOrcl(S), OrclL(ToOrcl(S))).main H.Count.init  ToOrcl(S).leaks.
  wp; call (: ={glob S, K.pk} /\ K.c{1} = H.Count.c{2}).
  + by proc; inline ToOrcl(S).orcl H.Count.incr; wp; call (: true); wp.
  by wp; call (: true); wp.
have ->:   Pr[CPAR(S, A).main() @ &m : res /\ K.c <= H.q]
         = Pr[INDR(ToOrcl(S),ToAdv(A)).main() @ &m : res /\ H.Count.c <= H.q].
+ byequiv (: ={glob A, glob S}
             ==> ={res,glob A, glob S, K.pk} /\ K.c{1} = H.Count.c{2})=> //.
  proc.
  inline ToAdv(A, ToOrcl(S), OrclR(ToOrcl(S))).main H.Count.init ToOrcl(S).leaks.
  wp; call (: ={glob S, K.pk} /\ K.c{1} = H.Count.c{2}).
  + by proc; inline ToOrcl(S).orcl H.Count.incr; wp; call (: true); wp.
  by wp; call (: true); wp.
have:= IND1_INDn (ToOrcl(S)) (ToAdv(A)) _ _ _ _ &m (fun ga go c, true)=> //=.
+ by proc; call Lkg.
+ by proc; call Lenc.
+ move=> O LR Llr Ll Lo; proc; call (La LR _)=> //.
  + by call Ll.
move=> <-; congr.
+ byequiv (: ={glob S,glob A} ==> ={res,glob H.HybOrcl} /\ K.c{1} = H.Count.c{2})=> //.
  proc.
  inline HybGame2(ToAdv(A), ToOrcl(S), OrclL(ToOrcl(S))).main H.Count.init.
  inline ToAdv(A, ToOrcl(S), HybOrcl2(ToOrcl(S), OrclL(ToOrcl(S)))).main.
  inline ToOrcl(S).leaks B(S, A, L(S)).main.
  wp; call (: ={glob S,glob H.HybOrcl, K.pk} /\ K.c{1} = H.Count.c{2}).
  + proc; wp; if=> //.
    + by call (: ={glob S, K.pk}); first sim.
    if=> //.
    + call (: ={glob S, K.pk} /\ K.c{1} = H.Count.c{2})=> //.
      by inline ToOrcl(S).orcl H.Count.incr; wp; call (: true); wp.
    by call (: ={glob S, K.pk}); first sim.
  swap{1} [4..5] -2; inline ToOrcl(S).leaks; wp.
  call(: true); auto; smt().
congr.
byequiv (: ={glob S,glob A} ==> ={res,glob H.HybOrcl} /\ K.c{1} = H.Count.c{2})=> //.
proc.
inline HybGame2(ToAdv(A), ToOrcl(S), OrclR(ToOrcl(S))).main H.Count.init.
inline ToAdv(A, ToOrcl(S), HybOrcl2(ToOrcl(S), OrclR(ToOrcl(S)))).main.
inline ToOrcl(S).leaks B(S, A, R(S)).main.
wp; call (: ={glob S,glob H.HybOrcl, K.pk} /\ K.c{1} = H.Count.c{2}).
+ proc; wp; if=> //.
  + by call (: ={glob S, K.pk}); first sim.
  if=> //.
  + call (: ={glob S, K.pk} /\ K.c{1} = H.Count.c{2})=> //.
    by inline ToOrcl(S).orcl H.Count.incr; wp; call (: true); wp.
  by call (: ={glob S, K.pk}); first sim.
swap {1} [4..5] -2; inline ToOrcl(S).leaks; wp.
by call (: true); auto; smt().
qed.
end section.

(* ==================================================================== *)
abstract theory WithCost.
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

module CPAL (S:Scheme) (A:AdvCPA) = {
  module A = A(L(S))

  proc main():bool = {
    var b':bool;

    (K.pk,K.sk) <@ S.kg();
    b'          <@ A.main(K.pk);
    return b';
  }
}.

module CPAR (S:Scheme) (A:AdvCPA) = {
  module A = A(R(S))

  proc main():bool = {
    var b':bool;
    (K.pk,K.sk) <@ S.kg();
    b'          <@ A.main(K.pk);
    return b';
  }
}.

module CPA (S:Scheme) (A:AdvCPA) = {
  proc main():bool = {
    var b':bool;
    K.b         <$ {0,1};
    (K.pk,K.sk) <@ S.kg();
    b'          <@ A(LRb(S)).main(K.pk);
    return b';
  }
}.

op q : { int | 0 < q } as q_gt0.

clone import Indist as Ind with
  type input <- plaintext,
  type H.output <- ciphertext,
  type H.inleaks <- unit,
  type H.outleaks <- pkey,
  op   H.q <= q

  proof H.q_ge0 by apply/ltzW/q_gt0.

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

module ToAdv(A:AdvCPA) (O:Orcl) (LR:LR) = {
  proc main() : bool = {
    var pk:pkey;
    var b':bool;
    pk <@ O.leaks();
    b' <@ A(LR).main(pk);
    return b';
  }
}.
module B (S:Scheme) (A:AdvCPA) (LR:LR) = {
  proc main(pk:pkey) : bool = {
    var b':bool;

    H.HybOrcl.l0 <$ [0..H.q-1];
    H.HybOrcl.l <- 0;
    b' <@ A(HybOrcl2(ToOrcl(S),LR)).main(pk);
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

schema cost_Hq `{P} : cost [P : H.q] = '0.
hint simplify cost_Hq.

section.
declare module S<:Scheme [ kg : `{N cs.`ckg}, enc: `{N cs.`cenc}] {-K, -H.Count, -H.HybOrcl}.
  (* Normaly I would like to locally
     clone Indist in the section, in that case
     restrictions at least on H.c are not needed.
     But LRB and B are used so we need to do it
   *)

declare module A <: AdvCPA [main : `{N cA, #LR.orcl: H.q}] {-K,-H.Count,-H.HybOrcl,-S}.

declare axiom La : forall (LR<:LR{-A}), islossless LR.orcl => islossless A(LR).main.

local lemma cost_AL : 
   choare [A(OrclL(ToOrcl(S))).main : H.Count.c = 0 ==> H.Count.c <= H.q] 
   time [N (H.q * cincr H.q);
         A.main : 1;
         S.enc  : H.q].
proof.
  proc (H.Count.c = k) :
       time [ OrclL(ToOrcl(S)).orcl k : [N (cincr H.q); S.enc : 1] ] => //.
  + by move => />; rewrite !bigi_constz 1..2:#smt:(H.q_ge0).
  move=> zo hzo; proc; inline *. 
  wp := (`|H.Count.c| <= H.q); call (: true); auto => &hr />.
  smt (cs_pos).
qed.

local lemma AL_bound : hoare [A(OrclL(ToOrcl(S))).main : H.Count.c = 0 ==> H.Count.c <= H.q].
proof. by conseq cost_AL. qed.

local lemma cost_AR : 
   choare [A(OrclR(ToOrcl(S))).main : H.Count.c = 0 ==> H.Count.c <= H.q] 
   time [N (H.q * cincr H.q);
         A.main : 1;
         S.enc  : H.q].
proof.
  proc (H.Count.c = k) : time
       [ OrclR(ToOrcl(S)).orcl k : [N (cincr H.q); S.enc : 1] ] => //.
  + by move => />; rewrite !bigi_constz 1..2:#smt:(H.q_ge0).
  move=> zo hzo; proc; inline *; wp; call(:true); wp:=(`|H.Count.c| <= H.q); skip => &hr />.
  smt(cs_pos).
qed.

local lemma AR_bound : hoare [A(OrclR(ToOrcl(S))).main : H.Count.c = 0 ==> H.Count.c <= H.q].
proof. by conseq cost_AR. qed.

local lemma cost_AHL : 
   choare [A(HybOrcl2(ToOrcl(S), OrclL(ToOrcl(S)))).main : 
       0 <= H.HybOrcl.l0 <= H.q /\ H.HybOrcl.l = 0 /\ H.Count.c = 0 ==> 
       H.HybOrcl.l <= H.q /\ H.Count.c <= 1 ]
    time [N (H.q * (cincr H.q + cincr 1 + cltint H.q + ceqint H.q)); S.enc : H.q; A.main : 1].
proof.
  proc 
    (H.HybOrcl.l = k /\ 0 <= H.HybOrcl.l0 <= H.q /\ H.Count.c = if H.HybOrcl.l <= H.HybOrcl.l0 then 0 else 1):
    time
    [ HybOrcl2(ToOrcl(S), OrclL(ToOrcl(S))).orcl k : [N(cincr H.q + cincr 1 + cltint H.q + ceqint H.q); S.enc : 1] ] => //=.
  + by rewrite !bigi_constz 1,2:#smt:(H.q_ge0).
  + by move=> &hr /> ->.
  + by move=> /> /#.
  move=> zo hzo; proc; inline *.
  wp := (`|H.HybOrcl.l| <= H.q).
  if := (`| H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q) => //. smt().
  + wp; call (:true; time []); auto => &hr />.
  smt (ge0_cincr ge0_cltint ge0_ceqint cs_pos).
  if := (`| H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q) => //. 
  + wp := (`|H.Count.c| <= 1); call (:true; time []); auto => &hr />.
    smt (ge0_cincr ge0_cltint ge0_ceqint cs_pos).
  by wp; call (:true; time []); auto => &hr />; smt (ge0_cincr ge0_cltint ge0_ceqint cs_pos).
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
    time [N (H.q * (cincr H.q + cincr 1 + cltint H.q + ceqint H.q)); S.enc : H.q; A.main : 1].
proof.
  proc 
    (H.HybOrcl.l = k /\ 0 <= H.HybOrcl.l0 <= H.q /\ H.Count.c = if H.HybOrcl.l <= H.HybOrcl.l0 then 0 else 1): time
    [ HybOrcl2(ToOrcl(S), OrclR(ToOrcl(S))).orcl k : [N (cincr H.q + cincr 1 + cltint H.q + ceqint H.q); S.enc : 1] ] => //=.
  + by rewrite !bigi_constz 1,2:#smt:(H.q_ge0).
  + by move=> &hr /> ->.
  + by move=> /> /#.
  move=> zo hzo; proc; inline *.
  wp := (`|H.HybOrcl.l| <= H.q).
  if := (`| H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q)=> //; 1: smt().
  + wp; call (:true; time []); auto => &hr />; smt (ge0_cincr ge0_cltint ge0_ceqint cs_pos).
  if := (`| H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q)=> //.
  + wp; call (:true; time []); wp := (`|H.Count.c| <= 1); skip => &hr />.
    smt (ge0_cincr ge0_cltint ge0_ceqint cs_pos).
  by wp; call (:true; time []); auto => &hr />; smt (ge0_cincr ge0_cltint ge0_ceqint cs_pos).
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
  have -> : Pr[CPAL(S, A).main() @ &m : res] =
            Pr[INDL(ToOrcl(S),ToAdv(A)).main() @ &m : res].
    byequiv (_ : ={glob A, glob S} ==>
                      ={res,glob A, glob S, K.pk}) => //.
    proc.
    inline ToAdv(A, ToOrcl(S), OrclL(ToOrcl(S))).main H.Count.init ToOrcl(S).leaks.
    wp;call (_: ={glob S, K.pk}).
      by proc;inline ToOrcl(S).orcl H.Count.incr;wp;call (_:true);wp.
    by wp;call (_:true);wp.
  have -> : Pr[CPAR(S, A).main() @ &m : res] =
            Pr[INDR(ToOrcl(S),ToAdv(A)).main() @ &m : res].
    byequiv (_ : ={glob A, glob S} ==>
                      ={res,glob A, glob S, K.pk}) => //.
    proc.
    inline ToAdv(A, ToOrcl(S), OrclR(ToOrcl(S))).main H.Count.init  ToOrcl(S).leaks.
    wp;call (_: ={glob S, K.pk}).
      by proc;inline ToOrcl(S).orcl H.Count.incr;wp;call (_:true);wp.
    by wp;call (_:true);wp.
  have := IND1_INDn (ToOrcl(S)) (ToAdv(A)) _ _ _ q_gt0 &m (fun ga go c, true) => //=.
  + have h : choare [ToOrcl(S).leaks : true ==> true] time ['0; S.kg:1].
    + by proc; call (_:true); skip => /=; smt(cs_pos).
    conseq h.
  + have h : choare [ToOrcl(S).orcl : true ==> true] time ['0; S.enc:1].
    + by proc; call (_:true); skip => /=; smt(cs_pos).
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
      proc; inline *; wp; call AHL_bound; auto; call(:true); auto=> />.
      smt (DInterval.supp_dinter q_gt0).
    byequiv (_: ={glob S,glob A} ==> ={res,glob H.HybOrcl}) => //.
    proc.
    inline
      H.Count.init
      CPAL(S, B(S, A)).A.main
      HybGame2(ToAdv(A), ToOrcl(S), OrclL(ToOrcl(S))).main.
    inline ToAdv(A, ToOrcl(S), HybOrcl2(ToOrcl(S), OrclL(ToOrcl(S)))).main.
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
    by call (_:true); auto=> />; smt(DInterval.supp_dinter q_gt0).
  have -> : Pr[INDR(ToOrcl(S), HybGame2(ToAdv(A))).main() @ &m : res /\ H.HybOrcl.l <= H.q /\ H.Count.c <= 1] =
            Pr[INDR(ToOrcl(S), HybGame2(ToAdv(A))).main() @ &m : res].
  + byequiv => //.
    conseq (_: ={glob A,glob S} ==> ={res}) (_: true ==>  H.HybOrcl.l <= H.q /\ H.Count.c <= 1) => //; last by sim.
    proc; inline *; wp; call AHR_bound; auto; call(:true); auto.
    smt (DInterval.supp_dinter q_gt0).
  byequiv (_: ={glob S,glob A} ==> ={res,glob H.HybOrcl}) => //.
  proc.
  inline
    H.Count.init
    CPAR(S, B(S,A)).A.main
    HybGame2(ToAdv(A), ToOrcl(S), OrclR(ToOrcl(S))).main.
  inline ToAdv(A, ToOrcl(S), HybOrcl2(ToOrcl(S), OrclR(ToOrcl(S)))).main.
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
  by call (_:true); auto=> />; smt (DInterval.supp_dinter q_gt0).
qed.

lemma big_b2i ['a] (P:'a -> bool) s : big predT (fun k => b2i (P k)) s = big P (fun _ => 1) s.
proof. by rewrite (big_mkcond P); apply congr_big. qed.

lemma bigi_b2i_split (k n m:int) P (F:int -> int):
  n <= k < m =>
  bigi P F n m = bigi P F n k + b2i (P k) * F k + bigi P F (k+1) m.
proof.
  move=> h; rewrite (big_cat_int k n m) 1,2:/#.
  rewrite (big_ltn_cond k m) 1:/# /b2i; case: (P k) => *; ring.
qed.

lemma bigi_inP (n m:int) P (F:int -> int):
  (forall i, n <= i < m => P i) =>
  bigi P F n m = bigi predT F n m.
proof. by move=> h; apply congr_big_int => // i /h ->. qed.

lemma bigi1 (n m:int) P (F:int -> int):
  (forall i, n <= i < m => P i => F i = 0) =>
  bigi P F n m = 0.
proof.
  by move=> h; apply big1_seq => i [] hP /mem_range hin; apply h.
qed.

lemma ex_CPA1_CPAn &m : 
  exists (B <: AdvCPA {+A,+H.HybOrcl, +K, +S}),
    (forall (clr:int) (MLR<:LR [orcl: `{N clr}] {-H.HybOrcl}),          
       choare[B(MLR).main : true ==> true] time
                [ N (H.q * (cincr H.q + ceqint H.q + cltint H.q) + cdinterval H.q);
                  S.enc: (H.q - 1);
                  A.main : 1;
                  MLR.orcl : 1]) /\
    Pr[CPAL(S,A).main() @ &m : res] - Pr[CPAR(S,A).main() @ &m : res] =
    H.q%r * (Pr[CPAL(S,B).main() @ &m : res] - Pr[CPAR(S,B).main() @ &m : res]).
proof.
  exists (B(S,A)); split; last by have -> := CPA1_CPAn &m; field; smt (q_gt0).
  move=> clr MLR.
  proc. 
  seq 2 : (H.HybOrcl.l =0 /\ 0 <= H.HybOrcl.l0 < H.q) time [ N (H.q * (cincr H.q + ceqint H.q + cltint H.q));
                                                             S.enc : (H.q - 1);
                                                             A.main : 1;
                                                             MLR.orcl : 1] => //.
  + wp. 
    instantiate /(_ H.q) /= h := (cost_dinterval {b' : bool, pk : pkey} 0 H.q).
    rnd (0 <= H.q <= H.q - 0); 1: by rewrite h.
    skip => &hr />.
    rewrite h /=.
    smt (DInterval.supp_dinter DInterval.dinter_ll q_gt0).
  exlim H.HybOrcl.l0 => l0. 
  call (: (H.HybOrcl.l = k /\ 0 <= H.HybOrcl.l0 <= H.q /\ l0 = H.HybOrcl.l0); time 
    [ HybOrcl2(ToOrcl(S), MLR).orcl k : [N (cincr H.q + ceqint H.q + cltint H.q); 
                                           S.enc : b2i (k <> l0); MLR.orcl : b2i(k=l0)] ]) => //=.
  + move=> zo hzo; proc; inline *; wp := (`|H.HybOrcl.l| <= H.q).
    if := (`|H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q) => //; 1: smt().
    + by wp; call (:true; time []); auto => &hr />; smt (ge0_ceqint). 
    if := (`|H.HybOrcl.l0| <= H.q /\ `|H.HybOrcl.l| <= H.q) => //. 
    + wp; call(:true; time []); auto => &hr /> /#.
    by wp; call (:true; time []); auto => &hr /> /#. 
  rewrite /=.
  skip => &hr />; move: (H.HybOrcl.l0{hr}) => {l0}l0 h0 hq .
  rewrite bigi_constz 1:#smt:(q_gt0) /=.
  rewrite !big_b2i !(bigi_b2i_split l0 0 H.q) 1,2:// /b2i /=.
  rewrite !(bigi_inP _ _ (fun (k : int) => k <> l0)) 1,2:/# !bigi_constz 1:// 1:/#.
  by rewrite !bigi1 /= /#.
qed.
end section.
