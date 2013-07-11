require import Int.
require import Real.
require import Map.
require import Set_Why.
require import CDH.
require Logic.
require Word.
require RandOrcl.
require PKE.


const k : int.

clone Word as Bitstring with op length = k.

type bitstring = Bitstring.word.

const qH : int.

axiom qH_pos : 0 < qH.

clone Set_CDH as SCDH with op n = qH.

import Group.
import Fset.
import FsetNth.

type pkey       = group.
type skey       = int.
type plaintext  = bitstring.
type ciphertext = group * bitstring.

op (^^) : bitstring -> bitstring -> bitstring = Bitstring.(^^).

op uniform : bitstring distr = Bitstring.Dword.dword.

lemma uniform_total (x:bitstring) : Distr.in_supp x uniform 
by [].

lemma uniform_spec (x y:bitstring) : Distr.mu_x uniform x = Distr.mu_x uniform y
by [].

clone import PKE as PKE_ with
  type pkey = pkey,
  type skey = skey,
  type plaintext = plaintext,
  type ciphertext = ciphertext. 

clone import RandOrcl as RandOrcl_group with 
  type from = group,
  type to = bitstring,
  op dsample = uniform,
  op qO = qH,
  op default = Bitstring.zeros.

import ROM.

(* Using Set_Why *)
theory WRO_Fset.

  module ARO (R:Oracle) : Oracle = {
    var log : from set

    fun init() : unit = {
      R.init();
      log = Fset.empty;
    }

    fun o(x:from) : to = {
      var r : to;

      if (card log < qO) {
        log = add x log;
        r = R.o(x);
      }
      else r = default;
      return r;
    }
  }.

end WRO_Fset.

import WRO_Fset.


module Hashed_ElGamal (O:Oracle) : Scheme = {
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

  fun dec(sk:skey, c:ciphertext) : plaintext Option.option = {
    var gy : group;
    var h, hm : bitstring;

    (gy, hm) = c; 
    h = O.o(gy ^ sk);
    return Option.Some (h ^^ hm); 
  }
}.


module type Adv (O:ARO) = {
  fun choose(pk:pkey)     : plaintext * plaintext
  fun guess(c:ciphertext) : bool
}.


module G1 (A_:Adv) = { 
  module S = Hashed_ElGamal(RO)
  module AO = ARO(RO)
  module A = A_(AO)
  
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
  [ CPA(Hashed_ElGamal(RO), A(ARO(RO)), ARO(RO)).main ~ G1(A).main : 
    (glob A){1} = (glob A){2} ==> !(mem G1.gxy ARO.log){2} => ={res} ].
proof.
  intros Hll1 Hll2; fun.
  inline ARO(RO).init G1(A).AO.init RO.init 
    Hashed_ElGamal(RO).kg Hashed_ElGamal(RO).enc.
  swap{1} 9 -5.
  seq 5 6 : 
    ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, y} /\
     RO.m{1} = Map.empty /\ ARO.log{2} = Fset.empty /\
     pk{1} = gx{2} /\ (G1.gxy = gx ^ y){2}).
  by wp; do rnd; wp; skip; smt.
  seq 2 2 : 
    ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m, y, b, m0, m1} /\
     pk{1} = gx{2} /\ (G1.gxy = gx ^ y){2} /\
     (forall x, mem x ARO.log <=> in_dom x RO.m){2}).

  rnd.
  call (_ : ={RO.m, ARO.log} /\ (forall x, mem x ARO.log <=> in_dom x RO.m){2}).
  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; progress; smt (* may timeout *).
  by wp; skip; smt.
  by skip; smt.

  call (_ : (mem G1.gxy ARO.log), 
       (={ARO.log} /\ eq_except RO.m{1} RO.m{2} G1.gxy{2})) => //.
  by intros O _; apply (Hll2 O) => //.
  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; smt.
  by wp; skip; smt.

  intros _ _; fun; if; inline RO.o; wp.
  by rnd Fun.cpTrue; wp; skip; smt.
  by wp; skip; smt.
  
  intros _; fun; if; inline RO.o; wp.
  by rnd Fun.cpTrue; wp; skip; smt.
  by wp; skip; smt.
  
  by inline RO.o; wp; rnd; wp; skip; progress; smt.
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


lemma G1_G2 (A <: Adv {G1, G2, RO, ARO, Hashed_ElGamal}) :
  equiv 
  [ G1(A).main ~ G2(A).main : 
    (glob A){1} = (glob A){2} ==> ={res, ARO.log} /\ G1.gxy{1} = G2.gxy{2} ].
proof.
  fun.
  inline G1(A).AO.init G2(A).AO.init RO.init.
  swap{2} 11 -3.
  call (_ : ={ARO.log, RO.m} /\ G1.gxy{1} = G2.gxy{2}).

  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; smt.
  by wp; skip; smt.
  wp.
  rnd (lambda h, h ^^ if b then m1 else m0){1}
      (lambda h, h ^^ if b then m1 else m0){1}.
  rnd.
  call ( _ : ={ARO.log, RO.m} /\ G1.gxy{1} = G2.gxy{2}).
  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; smt.
  by wp; skip; smt.
  wp; do rnd; wp; skip; progress=> //;first 2 by smt.
  case (bL) => _.
  cut -> : hL ^^ x2 ^^ x2 = hL ^^ (x2 ^^ x2); first by smt.
  by smt.
  cut -> : hL ^^ x1 ^^ x1 = hL ^^ (x1 ^^ x1); first by smt.
  by smt.
  case (bL) => _.
  cut -> : hR ^^ x2 ^^ x2 = hR ^^ (x2 ^^ x2); first by smt.
  by smt.
  cut -> : hR ^^ x1 ^^ x1 = hR ^^ (x1 ^^ x1); first by smt.
  by smt.
qed.

module SCDH_from_CPA (A_:Adv) : SCDH.Adversary = {
  module AO = ARO(RO)
  module A  = A_(AO)

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

(*
Already in Why3

lemma subset_card (s1 s2:'a set) : s1 <= s2 => #s1 <= #s2
by [].

lemma add_subset (x:'a) (s:'a set) : s <= add x s
by [].

lemma add_card_notmem (x:'a) (s:'a set) : !mem x s => #add x s = #s + 1
by [].

lemma add_card_mem (x:'a) (s:'a set) : mem x s => #s = 1 + #remove x s
by [].
*)

lemma add_mem (x:'a) (s:'a set) : mem x s => add x s = s
by (intros _; apply extensionality; smt).

lemma card_add (x:'a) (s:'a set) : card (add x s) <= card s + 1
by [].


lemma G2_SCDH (A <: Adv {CPA, G1, G2, SCDH.SCDH, RO, ARO, Hashed_ElGamal}) :
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  equiv 
  [ G2(A).main ~ SCDH.SCDH(SCDH_from_CPA(A)).main : 
    (glob A){1} = (glob A){2} ==> 
    (mem G2.gxy ARO.log){1} = res{2} /\ card ARO.log{1} <= qH ].
proof.
  intros _ _; fun.
  inline SCDH_from_CPA(A).solve SCDH_from_CPA(A).AO.init G2(A).AO.init RO.init.
  swap{2} [5..6] -4.  
  rnd{1}; wp.  
  seq 9 8 : 
    ((glob A){1} = (glob A){2} /\ ={ARO.log, RO.m} /\
    c{1} = (gy, h){2} /\ G2.gxy{1} = g ^ (x * y){2} /\ card ARO.log{1} <= qH).
  wp; rnd.
  call ( _ : ={ARO.log, RO.m} /\ card ARO.log{1} <= qH).
  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; smt.
  by wp; skip; smt.
  by wp; do rnd; wp; skip; smt.

  call ( _ : RO.m{1} = RO.m{2} /\ ARO.log{1} = ARO.log{2} /\ card ARO.log{1} <= qH).

  fun; inline RO.o; wp; if; first smt.
  by wp; rnd; wp; skip; smt.
  by wp; skip; smt.
  by skip; smt.
qed.


lemma Pr_CPA_G1 (A <: Adv {CPA, G1, G2, SCDH.SCDH, RO, ARO, Hashed_ElGamal}) &m :
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  Pr[CPA(Hashed_ElGamal(RO), A(ARO(RO)), ARO(RO)).main() @ &m : res] <=
  Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log]. 
proof.
  intros _ _.
  equiv_deno (CPA_G1 (A) _ _);try assumption; try smt.
qed.


lemma Pr_G1_G1 (A <: Adv {CPA, G1, G2, SCDH.SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log] <=
  Pr[G1(A).main() @ &m : res] + Pr[G1(A).main() @ &m : mem G1.gxy ARO.log].
proof.
  intros _ _. 
  apply (Trans 
    Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log]
    (Pr[G1(A).main() @ &m : res] + 
     Pr[G1(A).main() @ &m : mem G1.gxy ARO.log] -
     Pr[G1(A).main() @ &m : res /\ mem G1.gxy ARO.log])
    (Pr[G1(A).main() @ &m : res] + Pr[G1(A).main() @ &m : mem G1.gxy ARO.log]) 
     _ _).
  cut W: (forall (x y:real), x = y => x <= y); first smt.
  by apply W; rewrite Pr mu_or; smt.
  smt.
qed.

lemma Pr_G1_G2_res (A <: Adv {CPA, G1, G2, SCDH.SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  Pr[G1(A).main() @ &m : res] = Pr[G2(A).main() @ &m : res].
proof.
  equiv_deno (G1_G2 (A)); smt.
qed.


lemma Pr_G1_G2_mem (A <: Adv {CPA, G1, G2, SCDH.SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  Pr[G1(A).main() @ &m : mem G1.gxy ARO.log] = 
  Pr[G2(A).main() @ &m : mem G2.gxy ARO.log].
proof.
  equiv_deno (G1_G2 (A)); smt.
qed.


lemma islossless_AO : islossless ARO(RO).o.
proof.
  fun; inline ARO(RO).o RO.o; wp; if; wp.
  by rnd Fun.cpTrue; wp; skip; smt.
  by skip; trivial.
qed.


lemma Pr_G2 (A <: Adv {CPA, G1, G2, SCDH.SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  Pr[G2(A).main() @ &m : res] = 1%r / 2%r.
proof.
  intros Hll1 Hll2.
  bdhoare_deno (_ : true ==> _); [ | trivial | trivial ].
  fun; rnd ((=) b').
  call (_ : true) => //.
  by intros => O _;apply (Hll2 O) => //.
  by apply islossless_AO.
  wp; rnd Fun.cpTrue; call (_ : true).
  by intros => O _;apply (Hll1 O) => //.
  by apply islossless_AO.
  by wp; do rnd Fun.cpTrue; inline G2(A).AO.init RO.init; wp; skip; progress; smt.
qed.


lemma Pr_G2_SCDH (A <: Adv {CPA, G1, G2, SCDH.SCDH, RO, ARO, Hashed_ElGamal}) &m : 
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  Pr[G2(A).main() @ &m : mem G2.gxy ARO.log] =
  Pr[SCDH.SCDH(SCDH_from_CPA(A)).main() @ &m : res].
proof.
  intros _ _.
  equiv_deno (G2_SCDH (A) _ _); try assumption;trivial.
qed.


lemma Reduction (A <: Adv {CPA, G1, G2, SCDH.SCDH, RO, ARO, Hashed_ElGamal}) &m :  
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  Pr[CPA(Hashed_ElGamal(RO), A(ARO(RO)), ARO(RO)).main() @ &m : res] <=
  1%r / 2%r + Pr[SCDH.SCDH(SCDH_from_CPA(A)).main() @ &m : res].
proof. 
  intros _ _.  
  apply (Trans _ Pr[G1(A).main() @ &m : res \/ mem G1.gxy ARO.log]).
  by apply (Pr_CPA_G1 (A) &m); assumption.
  apply (Trans _
    (Pr[G1(A).main() @ &m : res] + Pr[G1(A).main() @ &m : mem G1.gxy ARO.log])).
  by apply (Pr_G1_G1 (A) &m); try assumption.
  rewrite (Pr_G1_G2_res (A) &m).
  rewrite (Pr_G2 (A) &m); try assumption. 
  rewrite (Pr_G1_G2_mem (A) &m).  
  rewrite (Pr_G2_SCDH (A) &m); try assumption.
  by apply Refl.
qed.

lemma Security (A <: Adv {CPA, G1, G2, SCDH.SCDH, RO, ARO, Hashed_ElGamal}) &m :
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  exists (B <: SCDH.Adversary),
    Pr[CPA(Hashed_ElGamal(RO), A(ARO(RO)), ARO(RO)).main() @ &m : res] - 1%r / 2%r <= 
    Pr[SCDH.SCDH(B).main() @ &m : res].
proof.
  intros _ _.
  exists ( SCDH_from_CPA(A)).
  cut W : (forall (x y z : real), x <= z + y => x - z <= y); first smt.
  by apply W; apply (Reduction (A) &m); assumption.
qed.


(** Composing reduction from CPA to SCDH with reduction from SCDH to CDH *)
lemma Security_CDH 
  (A <: Adv {CPA, G1, G2, SCDH.SCDH, RO, ARO, Hashed_ElGamal}) &m :
  (forall (O <: ARO), islossless O.o => islossless A(O).choose) =>
  (forall (O <: ARO), islossless O.o => islossless A(O).guess) =>
  exists (B <: CDH.Adversary),
    Pr[CPA(Hashed_ElGamal(RO), A(ARO(RO)), ARO(RO)).main() @ &m : res] - 1%r / 2%r 
    <= qH%r * Pr[CDH.CDH(B).main() @ &m : res].
proof.
  intros _ _.
  elim (Security (A) &m _ _); try assumption.
  intros B _.
  elim (SCDH.Reduction (B) &m _); first smt.
  intros C _.
  exists (C).
  apply (Trans _ Pr[SCDH.SCDH(B).main() @ &m : res]).
  assumption.
  apply SCDH.mult_inv_le_r; first smt.
  assumption.
qed.


lemma Correctness : 
  hoare [Correctness(Hashed_ElGamal(RO), RO).main : true ==> res].
proof.
  fun.
  inline Hashed_ElGamal(RO).kg Hashed_ElGamal(RO).enc Hashed_ElGamal(RO).dec. 
  inline RO.o RO.init.
  do (wp; rnd); wp; skip; progress; [smt | | smt | smt].
    cut ->: g ^ y ^ sk0 = g ^ sk0 ^ y; first smt.
    rewrite Map.get_setE Option.proj_some.
    cut ->: (y0 ^^ (y0 ^^ m{hr}) = (y0 ^^ y0) ^^ m{hr});first by smt.
    by smt.
qed.
