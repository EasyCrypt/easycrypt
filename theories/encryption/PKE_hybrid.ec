(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List FSet Finite Distr.
require import Indist.

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

module type AdvCPA(LR:LR) = {
  proc main(pk:pkey) : bool
}.

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
  proc main():bool = {
    var b':bool;

    K.c         <- 0;
    (K.pk,K.sk) <@ S.kg();
    b'          <@ A(L(S)).main(K.pk);
    return b';
  }
}.

module CPAR (S:Scheme) (A:AdvCPA) = {
  proc main():bool = {
    var b':bool;

    K.c         <- 0;
    (K.pk,K.sk) <@ S.kg();
    b'          <@ A(R(S)).main(K.pk);
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
declare module S <: Scheme {K, H.Count, H.HybOrcl}.
  (* Normaly I would like to locally
     clone Indist in the section, in that case
     restrictions at least on H.c are not needed.
     But LRB and B are used so we need to do it
   *)

declare module A <: AdvCPA {K,H.Count,H.HybOrcl,S}.

declare axiom Lkg  : islossless S.kg.
declare axiom Lenc : islossless S.enc.
declare axiom La   : forall (LR<:LR{A}), islossless LR.orcl => islossless A(LR).main.

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
  by call (: true); auto.
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
by call (: true); auto.
qed.
end section.
