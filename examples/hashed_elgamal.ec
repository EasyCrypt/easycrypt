require import Int.
require import Real.
require import FMap. 
require import FSet.
require import CDH.
require Logic.
require AWord.
require RandOrcl.
require PKE.

import OptionGet.


const k : int.

clone AWord as Bitstring with op length = k.

type bitstring = Bitstring.word.

const qH : int.

axiom qH_pos : 0 < qH.

clone Set_CDH as SCDH with op n = qH.

import Group.

type pkey       = group.
type skey       = int.
type plaintext  = bitstring.
type ciphertext = group * bitstring.

op (^^) : bitstring -> bitstring -> bitstring = Bitstring.(^).

clone import PKE as PKE_ with
  type pkey = pkey,
  type skey = skey,
  type plaintext = plaintext,
  type ciphertext = ciphertext. 

module type Hash = {
  fun init() : unit
  fun hash(x:group) : bitstring
}.

module Hashed_ElGamal (H:Hash) : Scheme = {
  fun kg() : pkey * skey = {
    var sk : int;
    H.init();
    sk = $[0..q-1];
    return (g ^ sk, sk);   
  }

  fun enc(pk:pkey, m:plaintext) : ciphertext = {
    var y : int;
    var h : plaintext;
    y = $[0..q-1];
    h = H.hash(pk ^ y);
    return (g ^ y, h ^^ m);
  }

  fun dec(sk:skey, c:ciphertext) : plaintext option = {
    var gy : group;
    var h, hm : bitstring;
    (gy, hm) = c; 
    h = H.hash(gy ^ sk);
    return Option.Some (h ^^ hm); 
  }
}.

op uniform : bitstring distr = Bitstring.Dword.dword.

clone import RandOrcl as RandOrcl_group with 
  type from = group,
  type to = bitstring,
  op dsample = uniform,
  op qO = qH,
  op default = Bitstring.zeros.

import ROM.
import WRO_Set.

(* ROM Adversary *)


module type Adversary (O:ARO) = {
  fun choose(pk:pkey)     : plaintext * plaintext {* O.o}
  fun guess(c:ciphertext) : bool
}.

module AO = ARO(RO).

module H : Hash = {
  fun init() : unit = { AO.init(); }
  fun hash(x:group) : bitstring = { var y : bitstring; y = RO.o(x); return y; }
}.

module S = Hashed_ElGamal(H).

section.

  declare module A_ : Adversary {RO, ARO, SCDH.SCDH'}.

  axiom lossless_choose (O <: ARO) : islossless O.o => islossless A_(O).choose.

  axiom lossless_guess (O <: ARO) : islossless O.o => islossless A_(O).guess.

  local module A = A_(AO).

  local module G1 = { 
    var gxy : group

    fun main() : bool = {
      var x, y : int;
      var gx : group;
      var m0, m1 : plaintext;
      var c : ciphertext;
      var b, b' : bool;
      var h, z : bitstring;   
      AO.init();
      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = A.choose(gx);
      b       = ${0,1};
      h       = $uniform;
      c       = (g ^ y, h ^^ (b ? m1 : m0));
      b'      = A.guess(c);
      return (b' = b);
    }
  }.

  local equiv CPA_G1 :
    CPA(S, A).main ~ G1.main : true ==> !(mem G1.gxy ARO.log){2} => ={res}.
  proof.
    fun.
    inline AO.init RO.init H.init Hashed_ElGamal(H).kg Hashed_ElGamal(H).enc.
    swap{1} 9 -5.
    seq 5 6 : 
      (={ARO.log, RO.m, y} /\
       RO.m{1} = FMap.Core.empty /\ ARO.log{2} = FSet.empty /\
       pk{1} = gx{2} /\ (G1.gxy = gx ^ y){2}); first by wp; do rnd; wp.
    seq 2 2 : 
      (={glob A, ARO.log, RO.m, y, b, m0, m1} /\
       pk{1} = gx{2} /\ (G1.gxy = gx ^ y){2} /\
       (forall x, mem x ARO.log <=> in_dom x RO.m){2}).   
      rnd.
      call (_ : ={RO.m, ARO.log} /\ (forall x, mem x ARO.log <=> in_dom x RO.m){2}).
        fun; inline RO.o; wp; if; first by smt.
          by wp; rnd; wp; skip; progress; smt.
          by wp.
      by skip; smt.

      call (_ : (mem G1.gxy ARO.log), 
                (={ARO.log} /\ eq_except RO.m{1} RO.m{2} G1.gxy{2})) => //.
        by intros O; apply (lossless_guess O).
   
        fun; inline RO.o; wp; if; first smt.
        wp; rnd; wp; skip; progress=> //; first 5 last; last 6 smt.
        by case (x = G1.gxy){2}; smt.
        by wp.
       
        intros _ _; fun; if; inline RO.o; wp.
        by rnd; wp; skip; smt.
        by wp.
        
        intros _; fun; if; inline RO.o; wp.
        by rnd; wp; skip; smt.
        by wp.

      by inline H.hash RO.o; wp; rnd; wp; skip; progress; smt.
  qed.

  local module G2 = {
    var gxy : group
   
    fun main() : bool = {
      var x, y : int;
      var gx : group;
      var m0, m1 : plaintext;
      var c : ciphertext;
      var b, b' : bool;
      var h, z : bitstring;
      AO.init();
      x        = $[0..q-1];
      y        = $[0..q-1];
      gx       = g ^ x; 
      gxy      = gx ^ y;
      (m0,m1)  = A.choose(gx);
      h        = $uniform;
      c        = (g ^ y, h);
      b'       = A.guess(c);
      b        = ${0,1};
      return (b' = b);
    }
  }.
   
   
  local equiv G1_G2 :
     G1.main ~ G2.main : true ==> ={res, ARO.log} /\ G1.gxy{1} = G2.gxy{2}.
  proof.
    fun.
    inline AO.init RO.init.
    swap{2} 11 -3.
    call (_ : ={ARO.log, RO.m} /\ G1.gxy{1} = G2.gxy{2}).
      fun; inline RO.o; wp; if; first smt.
        by wp; rnd; wp; skip; smt.
        by wp.
    wp.
    rnd (lambda h, h ^^ if b then m1 else m0){1}; rnd.
    call ( _ : ={ARO.log, RO.m} /\ G1.gxy{1} = G2.gxy{2}).
    fun; inline RO.o; wp; if; first smt.
      by wp; rnd; wp; skip; smt.
      by wp.
    wp; do rnd; wp; skip; progress=> //; smt.
  qed.
   
  local module SCDH_from_CPA : SCDH.Adversary = {
    fun solve(gx:group, gy:group) : group set = {
      var m0, m1 : plaintext;
      var h : bitstring;
      var b' : bool;
      AO.init();
      (m0,m1)  = A.choose(gx);
      h        = $uniform;
      b'       = A.guess((gy, h));
      return ARO.log;
    }
  }.
   
  local equiv G2_SCDH :
    G2.main ~ SCDH.SCDH(SCDH_from_CPA).main : 
    true ==> (mem G2.gxy ARO.log){1} = res{2} /\ card ARO.log{1} <= qH.
  proof.
    fun.
    inline SCDH_from_CPA.solve AO.init RO.init.
    swap{2} [5..6] -4.  
    rnd{1}; wp.  
    seq 9 8 : 
      ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m} /\
      c{1} = (gy, h){2} /\ G2.gxy{1} = g ^ (x * y){2} /\ card ARO.log{1} <= qH).
      wp; rnd; call ( _ : ={ARO.log, RO.m} /\ card ARO.log{1} <= qH).
      fun; inline RO.o; wp; if; first by smt.
        by wp; rnd; wp; skip; smt.
        by wp.
      by wp; do rnd; wp; skip; smt.
   
      call ( _ :
       RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\ card ARO.log{1} <= qH).
        fun; inline RO.o; wp; if; first smt.
          by wp; rnd; wp; skip; smt.
          by wp.
        by skip; smt.
  qed.
      
  local lemma Pr_CPA_G1 &m :
    Pr[CPA(S, A).main() @ &m : res] <=
    Pr[G1.main() @ &m : res \/ mem G1.gxy ARO.log]. 
  proof.
    by equiv_deno CPA_G1 => //; smt.
  qed.
      
  local lemma Pr_G1_G1 &m :
    Pr[G1.main() @ &m : res \/ mem G1.gxy ARO.log] <=
    Pr[G1.main() @ &m : res] + Pr[G1.main() @ &m : mem G1.gxy ARO.log].
  proof.
    apply (Trans _
      (Pr[G1.main() @ &m : res] + 
       Pr[G1.main() @ &m : mem G1.gxy ARO.log] -
       Pr[G1.main() @ &m : res /\ mem G1.gxy ARO.log])).
    cut W: (forall (x y:real), x = y => x <= y) by smt.
    by apply W; rewrite Pr mu_or; smt.
    by smt.
  qed.
   
  local lemma Pr_G1_G2_res &m : 
    Pr[G1.main() @ &m : res] = Pr[G2.main() @ &m : res].
  proof.
    by equiv_deno G1_G2=> //; smt.
  qed.
      
  local lemma Pr_G1_G2_mem &m : 
    Pr[G1.main() @ &m : mem G1.gxy ARO.log] = 
    Pr[G2.main() @ &m : mem G2.gxy ARO.log].
  proof.
    by equiv_deno G1_G2=> //; smt.
  qed.
  
  local lemma Pr_G2 &m : Pr[G2.main() @ &m : res] = 1%r / 2%r.
  proof.
    bdhoare_deno (_ : true ==> _) => //.
    fun; rnd ((=) b').
    call (_ : true) => //.
    by intros => O _; apply (lossless_guess O).
    by apply RO_lossless_o; smt.
    wp; rnd; call (_ : true).
    by intros => O _; apply (lossless_choose O).
    by apply RO_lossless_o; smt.
    by wp; do rnd; inline AO.init RO.init; wp; skip; progress; smt.
  qed.
      
  local lemma Pr_G2_SCDH &m : 
    Pr[G2.main() @ &m : mem G2.gxy ARO.log] =
    Pr[SCDH.SCDH(SCDH_from_CPA).main() @ &m : res].
  proof.
    by equiv_deno G2_SCDH.
  qed.
   
  local lemma Reduction &m :
    Pr[CPA(S, A).main() @ &m : res] <=
    1%r / 2%r + Pr[SCDH.SCDH(SCDH_from_CPA).main() @ &m : res].
  proof. 
    apply (Trans _ Pr[G1.main() @ &m : res \/ mem G1.gxy ARO.log]);
    first by apply (Pr_CPA_G1 &m).
    apply (Trans _
      (Pr[G1.main() @ &m : res] + Pr[G1.main() @ &m : mem G1.gxy ARO.log])).
    by apply (Pr_G1_G1 &m).
    by rewrite (Pr_G1_G2_res &m) (Pr_G2 &m) (Pr_G1_G2_mem &m) (Pr_G2_SCDH &m).
  qed.
   
  local lemma Security_SCDH &m :
    exists (B <: SCDH.Adversary {SCDH.SCDH'}),
      Pr[CPA(S, A).main() @ &m : res] - 1%r / 2%r <= 
      Pr[SCDH.SCDH(B).main() @ &m : res].
  proof.
    exists SCDH_from_CPA.
    cut W : forall (x y z : real), x <= z + y => x - z <= y by smt.
    by apply W; apply (Reduction &m).
  qed.
   
  lemma mult_inv_le_r (x y z:real) : 
    0%r < x => (1%r / x) * y <= z => y <= x * z
  by [].

  (** Composing reduction from CPA to SCDH with reduction from SCDH to CDH *)
  lemma Security &m :
    exists (B <: CDH.Adversary),
      Pr[CPA(S, A_(AO)).main() @ &m : res] - 1%r / 2%r <= 
      qH%r * Pr[CDH.CDH(B).main() @ &m : res].
  proof.
    elim (Security_SCDH &m) => B H.
    elim (SCDH.Reduction B &m _); first by smt.
    intros C H1; exists C.
    apply (Trans _ Pr[SCDH.SCDH(B).main() @ &m : res]) => //.
    by apply mult_inv_le_r; first smt.
  qed.
     
  lemma Correctness : 
    hoare [Correctness(S).main : true ==> res].
  proof.
    fun.
    inline Hashed_ElGamal(H).kg Hashed_ElGamal(H).enc Hashed_ElGamal(H).dec.
    inline H.hash RO.o H.init AO.init RO.init.
    by do (wp; rnd); wp; skip; progress; smt.
  qed.

end section.

print axiom Security.
