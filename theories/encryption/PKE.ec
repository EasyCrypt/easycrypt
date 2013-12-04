require import Int.
require import Real.
require import FSet.
require import ISet.
require import Pair.
require import Distr.
require import Monoid.
require import Indist.
require import Option.
require import List.

type pkey.
type skey.
type plaintext.
type ciphertext.

module type Scheme = {
  fun kg() : pkey * skey 
  fun enc(pk:pkey, m:plaintext)  : ciphertext 
  fun dec(sk:skey, c:ciphertext) : plaintext option  
}.

module Correctness (S:Scheme) = {
  fun main(m:plaintext) : bool = {
    var pk : pkey;
    var sk : skey;
    var c  : ciphertext;
    var m' : plaintext option;

    (pk, sk) = S.kg();
    c        = S.enc(pk, m);
    m'       = S.dec(sk, c); 
    return (m' = Some m);
  }
}.

module type LR = {
  fun orcl (m0 m1:plaintext) : ciphertext
}.

module type AdvCPA(LR:LR) = {
  fun main(pk:pkey) : bool
}.

module K = { 
  var c  : int
  var pk : pkey
  var sk : skey
  var b  : bool
}.
 
module L (S:Scheme) = {

  fun orcl (m0 m1:plaintext) : ciphertext = {
    var r : ciphertext;
    r = S.enc(K.pk,m0);
    K.c = K.c + 1;
    return r;
  }
}.

module R (S:Scheme) = {

  fun orcl (m0 m1:plaintext) : ciphertext = {
    var r : ciphertext;
    r = S.enc(K.pk,m1);
    K.c = K.c + 1;
    return r;
  }
}.

module LRb (S:Scheme) = {

  fun orcl (m0 m1:plaintext) : ciphertext = {
    var r : ciphertext;
    r = S.enc(K.pk,K.b?m0:m1);
    K.c = K.c + 1;
    return r;
  }
}.

module CPAL (S:Scheme,A:AdvCPA) = {
  module A = A(L(S))
  fun main():bool = {
    var b':bool;
    K.c = 0;
    (K.pk,K.sk) = S.kg();
    b' = A.main(K.pk);
    return b';
  }
}.

module CPAR (S:Scheme,A:AdvCPA) = {
  module A = A(R(S))
  fun main():bool = {
    var b':bool;
    K.c = 0;
    (K.pk,K.sk) = S.kg();
    b' = A.main(K.pk);
    return b';
  }
}.

module CPA (S:Scheme,A:AdvCPA) = {
  module A = A(LRb(S))
  fun main():bool = {
    var b':bool;
    K.c = 0;
    K.b = ${0,1};
    (K.pk,K.sk) = S.kg();
    b' = A.main(K.pk);
    return b';
  }
}.

clone import Indist as Ind with
  type input <- plaintext,
  type H.output <- ciphertext,
  type H.inleaks <- unit,
  type H.outleaks <- pkey.

module ToOrcl (S:Scheme) = {
  fun leaks (il:unit) : pkey = {
    (K.pk, K.sk) = S.kg();
    return K.pk;
  }
  fun orcl (m:plaintext) : ciphertext = {
    var c : ciphertext;
    c = S.enc(K.pk, m);
    return c;
  }
}.

module ToAdv(A:AdvCPA, O:Orcl,LR:LR) = {
  module A = A(LR)
  fun main() : bool = {
    var pk:pkey;
    var b':bool;
    pk = O.leaks(());
    b' =A.main(pk);
    return b';
  }
}.

module B (S:Scheme, A:AdvCPA, LR:LR) = {
  module A = A(LRB2(ToOrcl(S),LR))
  fun main(pk:pkey) : bool = {
    var b':bool;
    H.LRB.l0 = $[0..H.q-1];
    H.LRB.l  = 0;
    b' = A.main(pk);
    return b';
  }
}.

section.

  declare module S:Scheme {K, H.C, H.LRB}. 
    (* Normaly I would like to locally 
       clone Indist in the section, in that case
       restrictions at least on H.c are not needed.
       But LRB and B are used so we need to do it 
     *) 

  declare module A:AdvCPA {K,H.C,H.LRB,S}.

  axiom Lkg  : islossless S.kg.
  axiom Lenc : islossless S.enc. 
  axiom La   : forall (LR<:LR{A}), islossless LR.orcl => islossless A(LR).main.

  equiv CPAL_INDL (A0<:AdvCPA {K,H.C,S}) : 
        CPAL(S,A0).main ~ INDL(ToOrcl(S),ToAdv(A0)).main : ={glob A0, glob S} ==>
           ={res,glob A0, glob S, K.pk} /\ K.c{1} = H.C.c{2}.
  proof.
    fun. 
    inline INDL(ToOrcl(S), ToAdv(A0)).A.main H.C.init  ToOrcl(S).leaks.
    wp;call (_: ={glob S, K.pk} /\ K.c{1} = H.C.c{2}).
      by fun;inline ToOrcl(S).orcl H.C.incr;wp;call (_:true);wp.
    by wp;call (_:true);wp.
  qed.

  equiv CPAR_INDR (A0<:AdvCPA {K,H.C,S}) : 
        CPAR(S,A0).main ~ INDR(ToOrcl(S),ToAdv(A0)).main : ={glob A0, glob S} ==>
           ={res,glob A0, glob S, K.pk} /\ K.c{1} = H.C.c{2}.
  proof.
    fun. 
    inline INDR(ToOrcl(S), ToAdv(A0)).A.main H.C.init  ToOrcl(S).leaks.
    wp;call (_: ={glob S, K.pk} /\ K.c{1} = H.C.c{2}).
      by fun;inline ToOrcl(S).orcl H.C.incr;wp;call (_:true);wp.
    by wp;call (_:true);wp.
  qed.


  lemma CPA1_CPAn &m : 0 < H.q => 
    Pr[CPAL(S,B(S,A)).main() @ &m : res /\ H.LRB.l <= H.q /\ K.c <= 1] - 
    Pr[CPAR(S,B(S,A)).main() @ &m : res /\ H.LRB.l <= H.q /\ K.c <= 1] =
    1%r/H.q%r * (Pr[CPAL(S,A).main() @ &m : res /\ K.c <= H.q] -
                 Pr[CPAR(S,A).main() @ &m : res /\ K.c <= H.q]).
  proof.
    intros Hq.
    cut -> : Pr[CPAL(S, A).main() @ &m : res /\ K.c <= H.q] =
             Pr[INDL(ToOrcl(S),ToAdv(A)).main() @ &m : res /\ H.C.c <= H.q].
      by equiv_deno (CPAL_INDL A).
    cut -> : Pr[CPAR(S, A).main() @ &m : res /\ K.c <= H.q] =
             Pr[INDR(ToOrcl(S),ToAdv(A)).main() @ &m : res /\ H.C.c <= H.q].          
      by equiv_deno (CPAR_INDR A).
    cut := IND1_INDn (ToOrcl(S)) (ToAdv(A)) _ _ _ _ &m (lambda ga go c, true) => //=.
      by fun;call Lkg.
      by fun;call Lenc.    
      intros O LR Llr Ll Lo;fun;call (La LR _) => //.
      by call Ll.
    intros <-;congr.
      equiv_deno (_: ={glob S,glob A} ==> ={res,glob H.LRB} /\ K.c{1} = H.C.c{2}) => //.
      fun.
      inline INDR(ToOrcl(S), Ind.B(ToAdv(A))).A.main H.C.init CPAR(S, B(S,A)).A.main
        Ind.B(ToAdv(A), ToOrcl(S), OrclR(ToOrcl(S))).A.main.
      wp.
      call (_: ={glob S,glob H.LRB, K.pk} /\ K.c{1} = H.C.c{2}).
        fun;wp.
        if => //.
          by call (_: ={glob S, K.pk});first eqobs_in.
        if => //.
          call (_: ={glob S, K.pk} /\ K.c{1} = H.C.c{2}) => //.
          by inline ToOrcl(S).orcl H.C.incr;wp;call (_: true);wp.
        by call (_: ={glob S, K.pk});first eqobs_in.
      swap{1} [4..5] -2;inline ToOrcl(S).leaks;wp.
      by call (_:true);wp;rnd;wp.
    equiv_deno (_: ={glob S,glob A} ==> ={res,glob H.LRB} /\ K.c{1} = H.C.c{2}) => //.
    fun.
    inline INDL(ToOrcl(S), Ind.B(ToAdv(A))).A.main H.C.init CPAL(S, B(S,A)).A.main
      Ind.B(ToAdv(A), ToOrcl(S), OrclL(ToOrcl(S))).A.main.
    wp.
    call (_: ={glob S,glob H.LRB, K.pk} /\ K.c{1} = H.C.c{2}).
      fun;wp.
      if => //.
        by call (_: ={glob S, K.pk});first eqobs_in.
      if => //.
        call (_: ={glob S, K.pk} /\ K.c{1} = H.C.c{2}) => //.
        by inline ToOrcl(S).orcl H.C.incr;wp;call (_: true);wp.
      by call (_: ={glob S, K.pk});first eqobs_in.
    swap{1} [4..5] -2;inline ToOrcl(S).leaks;wp.
    by call (_:true);wp;rnd;wp.
  qed.

end section. 