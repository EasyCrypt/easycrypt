timeout 5.

require import Int.
require import Bool.
require import Map.
require import Set.
require import Real.
require import Logic.
require Word.
require RandOrcl.

op k : int.

clone Word as Bitstring with op length = k.

type bitstring = Bitstring.word.
type group.

op g  : group.
op q  : int.
op qH : int.

axiom q_pos  : 0 < q.
axiom qH_pos : 0 < qH.

type pkey       = group.
type skey       = int.
type plaintext  = bitstring.
type ciphertext = group * bitstring.

op (^) : group -> int -> group.

op (^^) : bitstring -> bitstring -> bitstring = Bitstring.(^^).

op zeros : bitstring = Bitstring.zeros.

op uniform : bitstring distr = Bitstring.Dword.dword.

axiom pow_mul : forall (x, y:int), (g ^ x) ^ y = g ^ (x * y).

lemma xor_absorb : forall (x:bitstring), x ^^ x = zeros by [].

lemma xor_zeros : forall (x:bitstring), zeros ^^ x = x by [].

lemma xor_assoc : forall (x, y, z:bitstring), x ^^ (y ^^ z) = (x ^^ y) ^^ z by [].

lemma uniform_total : forall (x:bitstring), Distr.in_supp x uniform by [].

lemma uniform_spec : 
  forall (x y:bitstring), Distr.mu_x uniform x = Distr.mu_x uniform y
by [].
 
clone RandOrcl as RandOrcl_group with 
  type from = group, 
  type to = bitstring,
  op dsample = uniform,
  op qO = qH,
  op default = zeros.

import RandOrcl_group.
import ROM.

module type PKE_Scheme = { 
  fun kg() : pkey * skey 
  fun enc(pk:pkey, m:plaintext)  : ciphertext 
  fun dec(sk:skey, c:ciphertext) : plaintext
}.

module type PKE_Adversary = { 
  fun choose(pk:pkey)     : plaintext * plaintext 
  fun guess(c:ciphertext) : bool                  
}.

module PKE_CPA (S:PKE_Scheme, A:PKE_Adversary) = {
  fun main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m0 : plaintext;
    var m1 : plaintext;
    var c  : ciphertext;
    var b  : bool;
    var b' : bool;

    (pk,sk) := S.kg();
    (m0,m1) := A.choose(pk);
    b        = ${0,1};
    c       := S.enc(pk, b ? m1 : m0);
    b'      := A.guess(c);
    return (b = b');
  } 
}.

module Hashed_ElGamal (O:Oracle) : PKE_Scheme = {
  fun kg() : pkey * skey = {
    var sk : int;
    sk = $[0..q-1];
    return (g ^ sk, sk);   
  }

  fun enc(pk:pkey, m:plaintext) : ciphertext = {
    var y : int;
    var h : plaintext;
    y = $[0..q-1];
    h := O.o(pk ^ y);
    return (g ^ y, h ^^ m);
  }

  fun dec(sk:skey, c:ciphertext) : plaintext = {
    var gy : group;
    var hm : bitstring;
    var h : bitstring;
    (gy, hm) = c; 
    h := O.o(gy ^ sk);
    return h ^^ hm; 
  }
}.

module PKE_Correctness (S:PKE_Scheme) = {
  fun main(m:plaintext) : bool = {
    var pk : pkey;
    var sk : skey;
    var c  : ciphertext;
    var m' : plaintext;

    (pk,sk) := S.kg();
    c  := S.enc(pk, m);
    m' := S.dec(sk, c); 
    return (m' = m);
  }
}.

module type SCDH_Adversary = {
  fun solve(gx:group, gy:group) : group set
}.

module SCDH (B:SCDH_Adversary) = {
  fun main() : bool = {
    var x : int;
    var y : int;
    var S : group set;

    x  = $[0..q-1]; 
    y  = $[0..q-1];
    S := B.solve(g ^ x, g ^ y);
    return (mem (g ^ (x * y)) S /\ Set.card S <= qH);
  }
}.

module type Adv (O:Oracle) = {
  fun choose(pk:pkey)     : plaintext * plaintext 
  fun guess(c:ciphertext) : bool                  
}.

module CPA (A_:Adv) = { 
  module S = Hashed_ElGamal(RO)
  module AO = ARO(RO)
  module A = A_(AO)

  fun main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m0 : plaintext;
    var m1 : plaintext;
    var c  : ciphertext;
    var b  : bool;
    var b' : bool;

    AO.init();
    (pk,sk) := S.kg();
    (m0,m1) := A.choose(pk);
    b        = ${0,1};
    c       := S.enc(pk, b ? m1 : m0);
    b'      := A.guess(c);
    return (b = b');
  }
}. 

module G1 (A_:Adv) = { 
  module S = Hashed_ElGamal(RO)
  module AO = ARO(RO)
  module A = A_(AO)
  
  var gxy : group

  fun main() : bool = {
    var x : int;
    var y : int;
    var gx : group;
    var m0 : plaintext;
    var m1 : plaintext;
    var h : bitstring;
    var z : bitstring;
    var b  : bool;
    var b' : bool;
    var c : ciphertext;

    AO.init();
    x = $[0..q-1];
   y = $[0..q-1];
    gx = g ^ x; 
    gxy = gx ^ y;
    (m0,m1) := A.choose(gx);
    b = ${0,1};
    h = $uniform;
    c = (g ^ y, h ^^ (b ? m1 : m0));
    b' := A.guess(c);
    return (b = b');
  }
}.

lemma CPA_G1 (A <: Adv {CPA, G1, RO, ARO, Hashed_ElGamal}) :
  (forall (O <: Oracle),
   bd_hoare[ O.o : true ==> true] = 1%r =>
   bd_hoare[ A(O).guess : true ==> true] = 1%r) =>
   equiv 
  [ CPA(A).main ~ G1(A).main : 
    (glob A){1} = (glob A){2} ==> !(mem G1.gxy ARO.log){2} => res{1} = res{2} ].
proof.
  intros H; fun. 
  inline CPA(A).AO.init G1(A).AO.init RO.init CPA(A).S.kg CPA(A).S.enc.
  swap{1} 9 -5.
  app 5 6 : 
    ((glob A){1} = (glob A){2} /\
     RO.m{1} = Map.empty /\ ARO.log{2} = Set.empty /\ ARO.log{1} = ARO.log{2} /\
     RO.m{1} = RO.m{2} /\ pk{1} = gx{2} /\ y{1} = y{2} /\ (G1.gxy = gx ^ y){2}).
  wp; *rnd; wp; skip; trivial.

  app 2 2 : 
    ((glob A){1} = (glob A){2} /\ RO.m{1} = RO.m{2} /\
     pk{1} = gx{2} /\ y{1} = y{2} /\ b{1} = b{2} /\ (m0,m1){1} = (m0,m1){2} /\
     (G1.gxy = gx ^ y){2} /\ ARO.log{1} = ARO.log{2} /\
     (forall (x:group), mem x ARO.log{2} <=> in_dom x RO.m{2})).
  rnd.
  call 
    ((glob A){1} = (glob A){2} /\ RO.m{1} = RO.m{2} /\ 
     ARO.log{1} = ARO.log{2} /\ pk{1} = pk{2} /\ 
     (forall (x:group), mem x ARO.log{2} <=> in_dom x RO.m{2}))
    ((glob A){1} = (glob A){2} /\ res{1} = res{2} /\ RO.m{1} = RO.m{2} /\
     ARO.log{1} = ARO.log{2} /\
     (forall (x:group), mem x ARO.log{2} <=> in_dom x RO.m{2})).
  fun 
    (RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\
     (forall (x:group), mem x ARO.log{2} <=> in_dom x RO.m{2})).
  trivial.
  trivial.
  fun; inline RO.init; wp; skip; trivial.  
  fun; inline RO.o; wp; if.
  trivial.
  wp; rnd; wp; skip; trivial (* may timeout *).
  wp; skip; trivial.
  skip; trivial.

  call 
    ((!mem G1.gxy ARO.log){2} =>
       (glob A){1} = (glob A){2} /\ c{1} = c{2} /\ ARO.log{1} = ARO.log{2} /\
       Map.eq_except RO.m{1} RO.m{2} G1.gxy{2})
    ((!mem G1.gxy ARO.log){2} => res{1} = res{2} /\ ARO.log{1} = ARO.log{2}).
  fun (mem G1.gxy ARO.log) 
     (ARO.log{1} = ARO.log{2} /\ Map.eq_except RO.m{1} RO.m{2} G1.gxy{2}).
  trivial.
  trivial.

  intros O _ _; apply (H (<:O) _); assumption.

  fun; inline RO.init; wp; skip; trivial.  

  intros _ _; admit.
  intros _.
  admit. (* memory hr does not exist; bug? *)

  fun; inline RO.o; wp; if.
  trivial.
  wp; rnd; wp; skip; trivial.
  wp; skip; trivial.

  intros _ _; admit.
  intros _; admit.

  inline RO.o; wp; rnd; wp; skip; trivial.
save.

module G2 (A_:Adv) = { 
  module S = Hashed_ElGamal(RO)
  module AO = ARO(RO)
  module A = A_(AO)
  
  var gxy : group

  fun main() : bool = {
    var x : int;
    var y : int;
    var gx : group;
    var m0 : plaintext;
    var m1 : plaintext;
    var h : bitstring;
    var z : bitstring;
    var b  : bool;
    var b' : bool;
    var c : ciphertext;

    AO.init();
    x = $[0..q-1];
    y = $[0..q-1];
    gx = g ^ x; 
    gxy = gx ^ y;
    (m0,m1) := A.choose(gx);
    h = $uniform;
    c = (g ^ y, h);
    b' := A.guess(c);
    b = ${0,1};
    return (b = b');
  }
}.

lemma G1_G2 (A <: Adv {G1, G2, RO, ARO, Hashed_ElGamal}) :
  equiv 
    [ G1(A).main ~ G2(A).main : (glob A){1} = (glob A){2} ==> 
      res{1} = res{2} /\ G1.gxy{1} = G2.gxy{2} /\ ARO.log{1} = ARO.log{2} ].
proof.
  fun.
  inline G1(A).AO.init G2(A).AO.init RO.init.
  swap{2} 11 -3.
  call  
    ((glob A){1} = (glob A){2} /\ G1.gxy{1} = G2.gxy{2} /\
     ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2} /\ c{1} = c{2}) 
    (res{1} = res{2} /\ G1.gxy{1} = G2.gxy{2} /\ ARO.log{1} = ARO.log{2}).
  fun (RO.m{1} = RO.m{2} /\ G1.gxy{1} = G2.gxy{2} /\ ARO.log{1} = ARO.log{2}).
  trivial.
  trivial.
  fun; inline RO.init; wp; skip; trivial.
  fun; inline RO.o; wp; if.
  trivial.
  wp; rnd; wp; skip; trivial.
  wp; skip; trivial.

  wp.
  rnd (lambda h, h ^^ if b{1} then m1{1} else m0{1}) 
      (lambda h, h ^^ if b{1} then m1{1} else m0{1}).
  rnd.
  call  
   ((glob A){1} = (glob A){2} /\ G1.gxy{1} = G2.gxy{2} /\
     ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2} /\ pk{1} = pk{2}) 
    (res{1} = res{2} /\ (glob A){1} = (glob A){2} /\ 
     G1.gxy{1} = G2.gxy{2} /\ ARO.log{1} = ARO.log{2} /\ RO.m{1} = RO.m{2}).
  fun (RO.m{1} = RO.m{2} /\ G1.gxy{1} = G2.gxy{2} /\ ARO.log{1} = ARO.log{2}).
  trivial. 
  trivial.
  fun; inline RO.init; wp; skip; trivial.
  fun; inline RO.o; wp; if.
  trivial.
  wp; rnd; wp; skip; trivial.
  wp; skip; trivial.

  wp; *rnd; wp; skip.
  *intros _; *split; [trivial | trivial | ].
  *intros _; *split; [trivial | trivial | ].
  *intros _; *split; [trivial | ].
  intros _ res1 res2.   
  elimT tuple2_ind res1; elimT tuple2_ind res2.
  *intros _; *split; trivial.
save.

module SCDH_from_CPA (A_:Adv) : SCDH_Adversary = {
  module AO = ARO(RO)
  module A = A_(AO)

  fun solve(gx:group, gy:group) : group set = {
    var m0 : plaintext;
    var m1 : plaintext;
    var h : plaintext;
    var b' : bool;

    AO.init();
    (m0,m1) := A.choose(gx);
    h = $uniform;
    b' := A.guess((gy, h));
    return ARO.log;
  }
}.

lemma G2_SCDH (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) :
  (forall (O <: Oracle),
   bd_hoare[ O.o : true ==> true] = 1%r =>
   bd_hoare[ A(O).guess : true ==> true] = 1%r) =>
  equiv 
    [ G2(A).main ~ SCDH(SCDH_from_CPA(A)).main : 
      (glob A){1} = (glob A){2} ==> 
      (mem G2.gxy ARO.log){1} = res{2} /\ card ARO.log{1} <= qH].
proof.
  intros H; fun.
  inline SCDH_from_CPA(A).solve SCDH_from_CPA(A).AO.init G2(A).AO.init RO.init.
  swap{2} [5..6] -4.  
  rnd{1}; wp.  
  app 9 8 : 
    ((glob A){1} = (glob A){2} /\ RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\
    c{1} = (gy, h){2} /\ G2.gxy{1} = g ^ (x * y){2} /\
    Set.card ARO.log{1} <= qH).
  wp; rnd.
  call 
   ((glob A){1} = (glob A){2} /\ RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\
    Set.card ARO.log{1} <= qH /\ pk{1} = pk{2})
   ((glob A){1} = (glob A){2} /\ RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\
    Set.card ARO.log{1} <= qH /\ res{1} = res{2}).
  fun (RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\ 
    Set.card ARO.log{1} <= qH).
  trivial.
  trivial.
  fun; inline RO.init; wp; skip; trivial.
  fun; inline RO.o; wp; if.
  trivial.
  wp; rnd; wp; skip; trivial.
  wp; skip; trivial.

  wp; *rnd; wp; skip; trivial.

  call 
   ((glob A){1} = (glob A){2} /\ RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\
    Set.card ARO.log{1} <= qH /\ c{1} = c{2})
   (ARO.log{1} = ARO.log{2} /\ Set.card ARO.log{1} <= qH).
  fun (RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\ Set.card ARO.log{1} <= qH).
  trivial.
  trivial.
  fun; inline RO.init; wp; skip; trivial.
  fun; inline RO.o; wp; if.
  trivial.
  wp; rnd; wp; skip; trivial.
  wp; skip; trivial.
  skip; trivial.
save.

lemma Pr_CPA_G1 (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: Oracle),
   bd_hoare[ O.o : true ==> true] = 1%r =>
   bd_hoare[ A(O).guess : true ==> true] = 1%r) =>
  Pr[CPA(A).main() @ &m : res] <= 
  Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log]. 
proof.
  intros H.
  equiv_deno (CPA_G1 (<:A) _).
  assumption.
  trivial.
  trivial.
save.

lemma Pr_G1_G1 (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: Oracle),
   bd_hoare[ O.o : true ==> true] = 1%r =>
   bd_hoare[ A(O).guess : true ==> true] = 1%r) =>
  Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log] =
  Pr[G1(A).main() @ &m : res] + 
  Pr[G1(A).main() @ &m : mem G1.gxy ARO.log].
proof.
  intros H. 
  admit. (* union bound *)
save.

lemma Pr_G1_G2_res (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  Pr[G1(A).main() @ &m : res] = Pr[G2(A).main() @ &m : res].
proof.
  equiv_deno (G1_G2 (<:A)); trivial.
save.

lemma Pr_G1_G2_mem (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  Pr[G1(A).main() @ &m : mem G1.gxy ARO.log] = 
  Pr[G2(A).main() @ &m : mem G2.gxy ARO.log].
proof.
  equiv_deno (G1_G2 (<:A)); trivial.
save.

lemma Pr_G2 (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: Oracle),
   bd_hoare[ O.o : true ==> true] = 1%r =>
   bd_hoare[ A(O).guess : true ==> true] = 1%r) =>
  Pr[G2(A).main() @ &m : res] = 1%r / 2%r.
proof.
  intros H.
  cut H1 : (bd_hoare[G2(A).main : true ==> res] = (1%r / 2%r)).
  fun; rnd (1%r / 2%r) (lambda b, b = b'); simplify.
  admit.
  bdhoare_deno H1; trivial.
save.

lemma Pr_G2_SCDH (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: Oracle),
   bd_hoare[ O.o : true ==> true] = 1%r =>
   bd_hoare[ A(O).guess : true ==> true] = 1%r) =>
  Pr[G2(A).main() @ &m : mem G2.gxy ARO.log] =
  Pr[SCDH(SCDH_from_CPA(A)).main() @ &m : res].
proof.
  intros H.
  equiv_deno (G2_SCDH (<:A) _).
  assumption.
  trivial.
  trivial.
save.

lemma Reduction (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: Oracle),
   bd_hoare[ O.o : true ==> true] = 1%r =>
   bd_hoare[ A(O).guess : true ==> true] = 1%r) =>
  Pr[CPA(A).main() @ &m : res] <=
  1%r / 2%r + Pr[SCDH(SCDH_from_CPA(A)).main() @ &m : res].
proof. 
  intros H.  
  apply (Real.Trans 
    Pr[CPA(A).main() @ &m : res] 
    Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log] 
    (1%r / 2%r + Pr[SCDH(SCDH_from_CPA(A)).main() @ &m : res]) _ _).
  apply (Pr_CPA_G1 (<:A) &m _); assumption.
  rewrite (Pr_G1_G1 (<:A) &m _); [assumption | ].
  rewrite (Pr_G1_G2_res (<:A) &m).
  rewrite (Pr_G2 (<:A) &m _); [assumption | ].
  rewrite (Pr_G1_G2_mem (<:A) &m).  
  rewrite (Pr_G2_SCDH (<:A) &m _); [assumption | ].
  apply Real.Refl.
save.

lemma Security (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m :
  (forall (O <: Oracle),
   bd_hoare[ O.o : true ==> true] = 1%r =>
   bd_hoare[ A(O).guess : true ==> true] = 1%r) =>
  exists (B<:SCDH_Adversary), 
    Pr[CPA(A).main() @ &m : res] - 1%r / 2%r <= 
    Pr[SCDH(SCDH_from_CPA(A)).main() @ &m : res].
proof.
  intros H.
  exists (<:SCDH_from_CPA(A)).
  cut aux : (forall (x, y:real), x <= 1%r / 2%r + y => x - 1%r / 2%r <= y). 
  trivial.
  apply (aux
   Pr[CPA(A).main() @ &m : res]
   Pr[SCDH(SCDH_from_CPA(A)).main() @ &m : res] _).
  apply (Reduction (<:A) &m _).
  assumption.
save.

lemma Correctness : 
  hoare [PKE_Correctness(Hashed_ElGamal(RO)).main : true ==> res].
proof.
  fun; inline Hashed_ElGamal(RO).kg Hashed_ElGamal(RO).enc.
  app 7 : (in_dom (g ^ (sk * y)) RO.m /\ 
           c = (g ^ y, (proj RO.m.[g ^ (sk * y)]) ^^ m)).
  inline RO.o; *(wp; rnd); skip; trivial.
  inline Hashed_ElGamal(RO).dec RO.o.
  wp; rnd; wp; skip; trivial.
save.
