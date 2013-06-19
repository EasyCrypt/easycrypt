require import Int.
require import Bool.
require import Map.
require import Set.
require import Real.
require Logic.
require Word.
require RandOrcl.

const k : int.

clone Word as Bitstring with op length = k.

type bitstring = Bitstring.word.
type group.

const g  : group.
const q  : int.
const qH : int.

axiom q_pos  : 0 < q.
axiom qH_pos : 0 < qH.

type pkey       = group.
type skey       = int.
type plaintext  = bitstring.
type ciphertext = group * bitstring.

op (^) : group -> int -> group.

op (^^) : bitstring -> bitstring -> bitstring = Bitstring.(^^).

op uniform : bitstring distr = Bitstring.Dword.dword.

const zeros : bitstring = Bitstring.zeros.

axiom pow_mul : forall (x, y:int), (g ^ x) ^ y = g ^ (x * y).

lemma xor_absorb : forall (x:bitstring), x ^^ x = zeros 
by [].

lemma xor_zeros : forall (x:bitstring), zeros ^^ x = x 
by [].

lemma xor_assoc : forall (x, y, z:bitstring), x ^^ (y ^^ z) = (x ^^ y) ^^ z 
by [].

lemma uniform_total : forall (x:bitstring), Distr.in_supp x uniform 
by [].

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
import WRO_Set.

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
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;

    (pk,sk) = S.kg();
    (m0,m1) = A.choose(pk);
    b       = ${0,1};
    c       = S.enc(pk, b ? m1 : m0);
    b'      = A.guess(c);
    return (b' = b);
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
    h = O.o(pk ^ y);
    return (g ^ y, h ^^ m);
  }

  fun dec(sk:skey, c:ciphertext) : plaintext = {
    var gy : group;
    var h, hm : bitstring;
    (gy, hm) = c; 
    h        = O.o(gy ^ sk);
    return h ^^ hm; 
  }
}.

module PKE_Correctness (S:PKE_Scheme) = {
  fun main(m:plaintext) : bool = {
    var pk : pkey;
    var sk : skey;
    var c  : ciphertext;
    var m' : plaintext;

    (pk,sk) = S.kg();
    c       = S.enc(pk, m);
    m'      = S.dec(sk, c); 
    return (m' = m);
  }
}.

module type SCDH_Adversary = {
  fun solve(gx:group, gy:group) : group set
}.

module SCDH (B:SCDH_Adversary) = {
  fun main() : bool = {
    var x, y : int;
    var s : group set;

    x = $[0..q-1]; 
    y = $[0..q-1];
    s = B.solve(g ^ x, g ^ y);
    return (mem (g ^ (x * y)) s /\ card s <= qH);
  }
}.

module type Adv (O:ARO) = {
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
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;

    AO.init();
    (pk,sk) = S.kg();
    (m0,m1) = A.choose(pk);
    b       = ${0,1};
    c       = S.enc(pk, b ? m1 : m0);
    b'      = A.guess(c);
    return (b' = b);
  }
}. 

module G1 (A_:Adv) = { 
  module S  = Hashed_ElGamal(RO)
  module AO = ARO(RO)
  module A  = A_(AO)
  
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

lemma CPA_G1 (A <: Adv {CPA, G1, RO, ARO, Hashed_ElGamal}) :
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  equiv 
  [ CPA(A).main ~ G1(A).main : 
    (glob A){1} = (glob A){2} ==> !(mem G1.gxy ARO.log){2} => ={res} ].
proof.
  intros H1 H2; fun. 
  inline CPA(A).AO.init G1(A).AO.init RO.init CPA(A).S.kg CPA(A).S.enc.
  swap{1} 9 -5.
  seq 5 6 : 
    ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, y} /\
     RO.m{1} = Map.empty /\ ARO.log{2} = Set.empty /\
     pk{1} = gx{2} /\ (G1.gxy = gx ^ y){2}).
  by wp; do rnd; wp; skip; smt.
  seq 2 2 : 
    ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, y, b, m0, m1} /\
     pk{1} = gx{2} /\ (G1.gxy = gx ^ y){2} /\
     (forall x, mem x ARO.log <=> in_dom x RO.m){2}).

  rnd.
  call 
    ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, pk} /\
     (forall x, mem x ARO.log <=> in_dom x RO.m){2})
    ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, res} /\
     (forall x, mem x ARO.log <=> in_dom x RO.m){2}).

  fun (={RO.m, ARO.log} /\ (forall x, mem x ARO.log <=> in_dom x RO.m){2}).
  smt.
  smt.

  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; progress; smt (* may timeout *).
  by wp; skip; smt.
  by skip; smt.

  call 
    ((!mem G1.gxy ARO.log){2} => 
     (glob A){1} = (glob A){2} /\ ={c, ARO.log} /\ 
     eq_except RO.m{1} RO.m{2} G1.gxy{2})
    ((!mem G1.gxy ARO.log){2} => ={res, ARO.log}).
  fun (mem G1.gxy ARO.log) (={ARO.log} /\ eq_except RO.m{1} RO.m{2} G1.gxy{2}).
  smt.
  smt.
  assumption.

  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; smt.
  by wp; skip; smt.

  intros _ _; fun; if; inline RO.o; wp.
  by rnd 1%r Fun.cPtrue; wp; skip; smt.
  by wp; skip; smt.
  
  intros _; fun; if; inline RO.o; wp.
  by rnd 1%r Fun.cPtrue; wp; skip; smt.
  by wp; skip; smt.
  
  by inline RO.o; wp; rnd; wp; skip; smt.
qed.

module G2 (A_:Adv) = { 
  module S  = Hashed_ElGamal(RO)
  module AO = ARO(RO)
  module A  = A_(AO)
  
  var gxy : group

  fun main() : bool = {
    var x, y : int;
    var gx : group;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;
    var h, z  : bitstring;
  
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

lemma G1_G2 (A <: Adv {G1, G2, RO, ARO, Hashed_ElGamal}) :
  equiv 
  [ G1(A).main ~ G2(A).main : 
    (glob A){1} = (glob A){2} ==> ={res,ARO.log} /\ G1.gxy{1} = G2.gxy{2} ].
proof.
  fun.
  inline G1(A).AO.init G2(A).AO.init RO.init.
  swap{2} 11 -3.
  call  
    ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, c} /\ G1.gxy{1} = G2.gxy{2})
    (={ARO.log, res} /\ G1.gxy{1} = G2.gxy{2}).
  fun (={ARO.log, RO.m} /\ G1.gxy{1} = G2.gxy{2}).
  smt.
  smt.

  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; smt.
  by wp; skip; smt.
  wp.
  rnd (lambda h, h ^^ if b then m1 else m0){1}
      (lambda h, h ^^ if b then m1 else m0){1}.
  rnd.
  call  
   ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, pk} /\ G1.gxy{1} = G2.gxy{2})
   ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, res} /\ G1.gxy{1} = G2.gxy{2}).
  fun (={ARO.log, RO.m} /\ G1.gxy{1} = G2.gxy{2}).
  smt. 
  smt.
  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; smt.
  by wp; skip; smt.
  by wp; do rnd; wp; skip; progress; smt.
qed.

module SCDH_from_CPA (A_:Adv) : SCDH_Adversary = {
  module AO = ARO(RO)
  module A  = A_(AO)

  fun solve(gx:group, gy:group) : group set = {
    var m0, m1 : plaintext;
    var h  : plaintext;
    var b' : bool;

    AO.init();
    (m0,m1)  = A.choose(gx);
    h        = $uniform;
    b'       = A.guess((gy, h));
    return ARO.log;
  }
}.

lemma G2_SCDH (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) :
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  equiv 
  [ G2(A).main ~ SCDH(SCDH_from_CPA(A)).main : 
    (glob A){1} = (glob A){2} ==> 
    (mem G2.gxy ARO.log){1} = res{2} /\ card ARO.log{1} <= qH ].
proof.
  intros H1 H2; fun.
  inline SCDH_from_CPA(A).solve SCDH_from_CPA(A).AO.init G2(A).AO.init RO.init.
  swap{2} [5..6] -4.  
  rnd{1}; wp.  
  seq 9 8 : 
    ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m} /\
    c{1} = (gy, h){2} /\ G2.gxy{1} = g ^ (x * y){2} /\ card ARO.log{1} <= qH).
  wp; rnd.
  call 
   ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, pk} /\ card ARO.log{1} <= qH)
   ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, res} /\ card ARO.log{1} <= qH).
  fun (={ARO.log, RO.m} /\ card ARO.log{1} <= qH).
  smt.
  smt.
  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; smt.
  by wp; skip; smt.

  by wp; do rnd; wp; skip; smt.

  call 
   ((glob A){1} = (glob A){2} /\ RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\
    card ARO.log{1} <= qH /\ c{1} = c{2})
   (ARO.log{1} = ARO.log{2} /\ card ARO.log{1} <= qH).
  fun (RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\ card ARO.log{1} <= qH).
  smt.
  smt.

  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; smt.
  by wp; skip; smt.
  by skip; smt.
qed.

lemma Pr_CPA_G1 (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m :
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  Pr[CPA(A).main() @ &m : res] <=
  Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log]. 
proof.
  intros H1 H2.
  equiv_deno (CPA_G1 (<:A) _ _).
  assumption.
  assumption.
  smt.
  smt.
qed.

lemma Pr_G1_G1 (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log] <=
  Pr[G1(A).main() @ &m : res] + Pr[G1(A).main() @ &m : mem G1.gxy ARO.log].
proof.
  intros H1 H2. 
  apply (Real.Trans 
    Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log]
    (Pr[G1(A).main() @ &m : res] + 
     Pr[G1(A).main() @ &m : mem G1.gxy ARO.log] -
     Pr[G1(A).main() @ &m : res /\ mem G1.gxy ARO.log])
    (Pr[G1(A).main() @ &m : res] + Pr[G1(A).main() @ &m : mem G1.gxy ARO.log]) 
     _ _).
  cut W: (forall (x y:real), x = y => x <= y); first smt.
  by apply W; pr_or; smt.
  smt.
qed.

lemma Pr_G1_G2_res (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  Pr[G1(A).main() @ &m : res] = Pr[G2(A).main() @ &m : res].
proof.
  equiv_deno (G1_G2 (<:A)); smt.
qed.

lemma Pr_G1_G2_mem (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  Pr[G1(A).main() @ &m : mem G1.gxy ARO.log] = 
  Pr[G2(A).main() @ &m : mem G2.gxy ARO.log].
proof.
  equiv_deno (G1_G2 (<:A)); smt.
qed.

lemma islossless_AO : islossless ARO(RO).o.
proof.
  fun; inline ARO(RO).o RO.o; wp; if; wp.
  by rnd 1%r Fun.cPtrue; wp; skip; smt.
  by skip; trivial.
qed.

lemma Pr_G2 (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  Pr[G2(A).main() @ &m : res] = 1%r / 2%r.
proof.
  intros H1 H2.
  bdhoare_deno (_ : true ==> _); [ | trivial | trivial ].
  fun; rnd (1%r / 2%r) ((=) b').
  call (true) (true).

  fun (true).
  by trivial.
  by trivial.
  assumption.
  by apply islossless_AO.
  wp; rnd 1%r Fun.cPtrue; call (true) (true).

  fun (true).
  by trivial.
  by trivial.
  assumption.
  by apply islossless_AO.
  by wp; do rnd 1%r Fun.cPtrue; inline G2(A).AO.init RO.init; wp; skip; smt.
qed.

lemma Pr_G2_SCDH (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  Pr[G2(A).main() @ &m : mem G2.gxy ARO.log] =
  Pr[SCDH(SCDH_from_CPA(A)).main() @ &m : res].
proof.
  intros _ _.
  equiv_deno (G2_SCDH (<:A) _ _).
  assumption.
  assumption.
  by trivial.
  smt.
qed.

lemma Reduction (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  Pr[CPA(A).main() @ &m : res] <=
  1%r / 2%r + Pr[SCDH(SCDH_from_CPA(A)).main() @ &m : res].
proof. 
  intros H1 H2.  
  apply (Real.Trans 
    Pr[CPA(A).main() @ &m : res]
    Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log]
    (1%r / 2%r + Pr[SCDH(SCDH_from_CPA(A)).main() @ &m : res]) _ _).
  by apply (Pr_CPA_G1 (<:A) &m _ _); assumption.
  apply (Real.Trans
    Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log]
    (Pr[G1(A).main() @ &m : res] + Pr[G1(A).main() @ &m : mem G1.gxy ARO.log])
    (1%r / 2%r + Pr[SCDH(SCDH_from_CPA(A)).main() @ &m : res]) _ _).
  by apply (Pr_G1_G1 (<:A) &m _ _); try assumption.
  rewrite (Pr_G1_G2_res (<:A) &m).
  rewrite (Pr_G2 (<:A) &m _ _); try assumption. 
  rewrite (Pr_G1_G2_mem (<:A) &m).  
  rewrite (Pr_G2_SCDH (<:A) &m _ _); try assumption.
  by apply Real.Refl.
qed.

lemma Security (A <: Adv {CPA, G1, G2, SCDH, RO, ARO, Hashed_ElGamal}) &m :
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  exists (B <: SCDH_Adversary), 
    Pr[CPA(A).main() @ &m : res] - 1%r / 2%r <= Pr[SCDH(B).main() @ &m : res].
proof.
  intros H1 H2.
  exists (<: SCDH_from_CPA(A)).
  cut W : (forall (x, y:real), x <= 1%r / 2%r + y => x - 1%r / 2%r <= y). 
  smt.
  by apply W; apply (Reduction (<:A) &m _ _); assumption.
qed.

lemma Correctness : 
  hoare [PKE_Correctness(Hashed_ElGamal(RO)).main : true ==> res].
proof.
  fun; inline Hashed_ElGamal(RO).kg Hashed_ElGamal(RO).enc.
  seq 7 :
   (in_dom (g ^ (sk * y)) RO.m /\ c = (g ^ y, (proj RO.m.[g ^ (sk * y)]) ^^ m)).
  by inline RO.o; do (wp; rnd); skip; smt.
  inline Hashed_ElGamal(RO).dec RO.o.
  by wp; rnd; wp; skip; smt.
qed.
