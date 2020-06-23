(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List Distr DBool LorR.
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

module type Adversary = {
  proc choose(pk:pkey)     : plaintext * plaintext
  proc guess(c:ciphertext) : bool
}.

module CPA (S:Scheme, A:Adversary) = {
  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;

    (pk, sk) <@ S.kg();
    (m0, m1) <@ A.choose(pk);
    b        <$ {0,1};
    c        <@ S.enc(pk, b ? m1 : m0);
    b'       <@ A.guess(c);
    return (b' = b);
  }
}.

module CPA_L (S:Scheme, A:Adversary) = {
  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b' : bool;

    (pk, sk) <@ S.kg();
    (m0, m1) <@ A.choose(pk);
    c        <@ S.enc(pk, m0);
    b'       <@ A.guess(c);
    return b';
  }
}.

module CPA_R (S:Scheme, A:Adversary) = {
  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b' : bool;

    (pk, sk) <@ S.kg();
    (m0, m1) <@ A.choose(pk);
    c        <@ S.enc(pk, m1);
    b'       <@ A.guess(c);
    return b';
  }
}.

section.

  declare module S:Scheme.
  declare module A:Adversary{-S}.

  lemma pr_CPA_LR &m: 
    islossless S.kg => islossless S.enc =>
    islossless A.choose => islossless A.guess => 
    `| Pr[CPA_L(S,A).main () @ &m : res] - Pr[CPA_R(S,A).main () @ &m : res] | =
     2%r * `| Pr[CPA(S,A).main() @ &m : res] - 1%r/2%r |.
  proof.
    move => kg_ll enc_ll choose_ll guess_ll.
    have -> : Pr[CPA(S, A).main() @ &m : res] = 
              Pr[RandomLR(CPA_R(S,A), CPA_L(S,A)).main() @ &m : res].
    + byequiv (_ : ={glob S, glob A} ==> ={res})=> //.
      proc.      
      swap{1} 3-2; seq 1 1 : (={glob S, glob A, b}); first by rnd.
      if{2}; inline *; wp; do 4! call (_: true); auto => /> /#.
    rewrite -(pr_AdvLR_AdvRndLR (CPA_R(S,A)) (CPA_L(S,A)) &m) 2:/#.
    byphoare => //; proc.
    by call guess_ll; call enc_ll; call choose_ll; call kg_ll.
  qed.

end section.

(*
** Based on lists. Several versions can be given as in RandOrcl.
** Also, oracle annotations could be used to provide different oracles during
** the choose and guess stages of the experiment.
*)

module type CCA_ORC = {
  proc dec(c:ciphertext) : plaintext option
}.

module type CCA_ADV (O:CCA_ORC) = {
  proc choose(pk:pkey)     : plaintext * plaintext {O.dec}
  proc guess(c:ciphertext) : bool {O.dec}
}.

module CCA (S:Scheme, A:CCA_ADV) = {
  var log   : ciphertext list
  var cstar : ciphertext option
  var sk    : skey

  module O = {
    proc dec(c:ciphertext) : plaintext option = {
      var m : plaintext option;

      if (Some c <> cstar) m <@ S.dec(sk, c);
      else m <- None;
      return m;
    }
  }

  module A = A(O)

  proc main() : bool = {
    var pk : pkey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;

    cstar    <- None;
    (pk, sk) <@ S.kg();
    (m0, m1) <@ A.choose(pk);
    b        <$ {0,1};
    c        <@ S.enc(pk, b ? m1 : m0);
    cstar    <- Some c;
    b'       <@ A.guess(c);
    return (b' = b);
  }
}.

module CCAl (S:Scheme, A:CCA_ADV) = {

  module O = {
    proc dec(c:ciphertext) : plaintext option = {
      var m : plaintext option;

      if (Some c <> CCA.cstar) {
        CCA.log <- c :: CCA.log;
        m   <@ S.dec(CCA.sk, c);
      }
      else m <- None;
      return m;
    }
  }

  module A = A(O)

  proc main() : bool = {
    var pk : pkey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;

    CCA.log      <- [];
    CCA.cstar    <- None;
    (pk, CCA.sk) <@ S.kg();
    (m0, m1) <@ A.choose(pk);
    b        <$ {0,1};
    c        <@ S.enc(pk, b ? m1 : m0);
    CCA.cstar    <- Some c;
    b'       <@ A.guess(c);
    return (b' = b);
  }
}.

section.

declare module S: Scheme {-CCA}.

declare module A: CCA_ADV {-CCA, -S}.

equiv eq_CCA_CCAl : CCA(S,A).main ~ CCAl(S,A).main : ={glob S, glob A} ==> ={res, glob S, glob A, CCA.sk, CCA.cstar}.
proof. by sim. qed.

end section.

(* Complexity of the adversary *)
type cost_A = {
  cchoose   : int;
  qD_choose : int;
  cguess    : int;
  qD_guess  : int;
}.

type cost_S = {
  ckg  : int;
  cenc : int;
  cdec : int;
}.

abstract theory CCA_q.

op cA : cost_A.

axiom ge0_cA : 0 <= cA.`cchoose /\ 0 <= cA.`qD_choose /\ 0 <= cA.`cguess /\ 0 <= cA.`qD_guess.

op qD = cA.`qD_choose + cA.`qD_guess.

lemma ge0_qD : 0 <= qD by smt (ge0_cA).

op cS : cost_S.

axiom ge0_cS : 0 <= cS.`ckg /\ 0 <= cS.`cenc /\ 0 <= cS.`cdec.

op ceqocipher : int.

schema cost_eqcipher `{P} {c1 c2 : ciphertext option} : cost [P : c1 = c2] = cost[P:c1] + cost[P:c2] + ceqocipher .
hint simplify cost_eqcipher.

module CCAq (S:Scheme, A:CCA_ADV) = {
 
  module O = {
    proc dec(c:ciphertext) : plaintext option = {
      var m : plaintext option;

      if (size CCA.log < qD && (Some c <> CCA.cstar)) {
        CCA.log <- c :: CCA.log;
        m   <@ S.dec(CCA.sk, c);
      }
      else m <- None;
      return m;
    }
  }

  module A = A(O)

  proc main() : bool = {
    var pk : pkey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;

    CCA.log      <- [];
    CCA.cstar    <- None;
    (pk, CCA.sk) <@ S.kg();
    (m0, m1) <@ A.choose(pk);
    b        <$ {0,1};
    c        <@ S.enc(pk, b ? m1 : m0);
    CCA.cstar    <- Some c;
    b'       <@ A.guess(c);
    return (b' = b);
  }
}.

section.

declare module S: Scheme [kg  : `{cS.`ckg},
                          enc : `{cS.`cenc}, 
                          dec : `{cS.`cdec} ]
                         {-CCA}.

lemma Sdec_ll : islossless S.dec.
proof.
have h : choare [S.dec : true ==> true] time [cS.`cdec].
+ by proc true : time [].
conseq h.
qed.

lemma Senc_ll : islossless S.enc.
proof.
have h : choare [S.enc : true ==> true] time [cS.`cenc].
+ by proc true : time [].
conseq h.
qed.

declare module A : CCA_ADV [choose : `{cA.`cchoose, #O.dec : cA.`qD_choose},
                            guess  : `{cA.`cguess, #O.dec : cA.`qD_guess}]
                           {-CCA, -S}.

axiom Achoose_ll : forall (O <: CCA_ORC {-A}), islossless O.dec => islossless A(O).choose.
axiom Aguess_ll : forall (O <: CCA_ORC {-A}), islossless O.dec => islossless A(O).guess.

lemma CCAl_cbound : choare [CCAl(S,A).main : true ==> size CCA.log <= qD] time 
                          [ 5 + cdbool + (3 + ceqocipher) * cA.`qD_guess +  (3 + ceqocipher) * cA.`qD_choose;
                            S.kg  : 1; S.enc : 1; S.dec : qD;
                            A.choose : 1; A.guess  : 1].
proof.
  proc.
  call (:true; 
         (CCAl(S,A).O.dec : size CCA.log - cA.`qD_choose) 
           time
           [(CCAl(S,A).O.dec : [fun _ => 3 + ceqocipher; S.dec: fun _ => 1])]).
  + move=> zdec hzdec; proc.
    if. 
    + by call (:true; time []); auto => &hr /> * /#.
    by auto => &hr />; smt(ge0_cS).
  wp; call (:true; time []); rnd.
  call (:true; 
         (CCAl(S,A).O.dec : size CCA.log) 
           time
           [(CCAl(S,A).O.dec : [fun _ => 3 + ceqocipher; S.dec: fun _ => 1])]).
  + move=> zdec hzdec; proc.
    if. 
    + by call (:true; time []); auto => &hr /> * /#.
    by auto => &hr />; smt(ge0_cS).
  call(:true; time[]); auto => />. rewrite dbool_ll /=; split. smt().
  by rewrite !bigi_constz; smt(ge0_cA).
qed.

lemma CCAl_bound : hoare [CCAl(S,A).main : true ==> size CCA.log <= qD].
proof. conseq CCAl_cbound. qed.

equiv CCAq_CCAl : CCAq(S,A).main ~ CCAl(S,A).main : ={glob A, glob S} ==> ={res, glob S, glob A, glob CCA}.
proof.
  conseq (_: ={glob A, glob S} ==> size CCA.log{2} <= qD => ={res, glob S, glob A, glob CCA}) 
    _ (CCAl_bound) => //.
  proc.  
  seq 5 5 : (={b} /\ (size CCA.log{2} <= qD => ={pk, m0, m1, glob S, glob A, glob CCA})).
  rnd; call (: qD < size CCA.log, ={glob S, glob CCA}) => //=.
  + by apply Achoose_ll.  
  + proc; if{2}; last by rcondf{1} ^if; auto.
    if{1}; 1: by call (:true); auto.
    by call{2} Sdec_ll; auto => /> /#.
  + by move=> _ _; islossless; apply Sdec_ll.
  + proc; if; auto.
    by call Sdec_ll; auto => /#.
  call (:true); auto => />; smt().

  call (: qD < size CCA.log, ={glob S, glob CCA}) => //=.
  + by apply Aguess_ll.  
  + proc; if{2}; last by rcondf{1} ^if; auto.
    if{1}; 1: by call (:true); auto.
    by call{2} Sdec_ll; auto => /> /#.
  + by move=> _ _; islossless; apply Sdec_ll.
  + proc; if; auto.
    by call Sdec_ll; auto => /#.
  
  wp; case: (size CCA.log{2} <= qD).
  + by call (:true); auto => /> /#.
  by call{1} Senc_ll; call{2} Senc_ll; skip => /> /#.
qed.

equiv CCA_CCAq : CCA(S,A).main ~ CCAq(S,A).main : ={glob A, glob S} ==> ={res, glob S, glob A, CCA.sk, CCA.cstar}.
proof.
  transitivity CCAl(S,A).main
     (={glob A, glob S} ==> ={res, glob S, glob A, CCA.sk, CCA.cstar})
     (={glob A, glob S} ==> ={res, glob S, glob A, glob CCA})=> //; 1: smt().
  + by sim.
  by symmetry; conseq CCAq_CCAl.
qed.

