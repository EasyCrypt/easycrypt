require import Pred.
require import Distr.
require import Int.
require import Real.
require import FMap. 
require import FSet.
require (*--*) CDH.
require (*--*) AWord.
require (*--*) ROM.
require (*--*) PKE.

(* The type of plaintexts: bitstrings of length k *)
type bits.
op k: int.
axiom k_pos: 0 < k.

op uniform: bits distr.
axiom uniformU: isuniform uniform.
axiom uniformX x: mu uniform ((=) x) = 1%r/(2^k)%r.
axiom uniformL: mu uniform True = 1%r.

op (^^): bits -> bits -> bits.

clone import AWord as Bitstring with
  type word <- bits,
  op length <- k,
  op (^) <- (^^),
  op Dword.dword <- uniform
proof
  Dword.*     by smt,
  leq0_length by smt.

(* Upper bound on the number of calls to H *)
op qH: int.
axiom qH_pos: 0 < qH.

(* Assumption *)
clone import CDH.Set_CDH as SCDH with
  op n <- qH.

import Group.

type pkey       = group.
type skey       = int.
type plaintext  = bits.
type ciphertext = group * bits.

clone import PKE as PKE_ with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext. 

module type Hash = {
  proc init(): unit
  proc hash(x:group): bits
}.

module Hashed_ElGamal (H:Hash): Scheme = {
  proc kg(): pkey * skey = {
    var sk;

    H.init();
    sk = $[0..q-1];
    return (g ^ sk, sk);   
  }

  proc enc(pk:pkey, m:plaintext): ciphertext = {
    var y, h;

    y = $[0..q-1];
    h = H.hash(pk ^ y);
    return (g ^ y, h ^^ m);
  }

  proc dec(sk:skey, c:ciphertext): plaintext option = {
    var gy, h, hm;

    (gy, hm) = c; 
    h = H.hash(gy ^ sk);
    return Option.Some (h ^^ hm); 
  }
}.

clone import ROM.ROM_BadCall as ROC with
  type from  <- group,
  type to    <- bits,
  op dsample <- fun (x:group), uniform,
  op qH      <- qH
proof * by smt.

(* Adversary Definitions *)
module type Adversary (O:ARO) = {
  proc choose(pk:pkey)    : plaintext * plaintext
  proc guess(c:ciphertext): bool
}.

(* Specializing and merging the hash function *)
module H:Hash = {
  proc init(): unit = { RO.init(); Log.qs = FSet.empty; }
  proc hash(x:group): bits = { var y; y = RO.o(x); return y; }
}.

(* The initial scheme *)
module S = Hashed_ElGamal(H).

(* Correctness result *)
hoare Correctness: Correctness(S).main: true ==> res.
proof. by proc; inline *; auto; progress; smt. qed.

(* The reduction *)
module SCDH_from_CPA(A:Adversary,O:Oracle): Top.SCDH.Adversary = {
  module BA = A(Bound(O))

  proc solve(gx:group, gy:group): group set = {
    var m0, m1, h, b';

    H.init();
    (m0,m1)  = BA.choose(gx);
    h        = $uniform;
    b'       = BA.guess(gy, h);
    return Log.qs;
  }
}.

(* We want to bound the probability of A winning CPA(Bounder(A,RO),S) in terms of
   the probability of B = CDH_from_CPA(SCDH_from_CPA(A,RO)) winning CDH(B) *)
section.
  declare module A: Adversary {RO, Log, OnBound.G1, OnBound.G2}.

  axiom chooseL (O <: ARO {A}): islossless O.o => islossless A(O).choose.
  axiom guessL (O <: ARO {A}) : islossless O.o => islossless A(O).guess.

  local module BA = A(Bound(RO)).

  local module G0 = {
    var gxy:group

    proc main(): bool = {
      var m0, m1, c, b, b';
      var x, y, h, gx;

      H.init();
      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = BA.choose(gx);
      b       = ${0,1};
      h       = H.hash(gxy);
      c       = (g ^ y, h ^^ (b ? m1 : m0));
      b'      = BA.guess(c);
      return (b' = b);
    }
  }.

  local equiv CPA_G0: CPA(S,BA).main ~ G0.main: ={glob A} ==> ={res}.
  proof.
    proc.
    inline Hashed_ElGamal(H).kg Hashed_ElGamal(H).enc.
    swap{1} 8 -5.
    call (_: ={glob H, Log.qs}); first by sim.
    wp; call (_: ={glob H}); first by sim.
    wp; rnd.
    call (_: ={glob H, Log.qs}); first by sim.
    wp; do !rnd.
    by call (_: true ==> ={glob H}); first by sim.
  qed.

  local lemma Pr_CPA_G0 &m:
    Pr[CPA(S,BA).main() @ &m: res] = Pr[G0.main() @ &m: res]
  by byequiv CPA_G0.

  local module G1 = { 
    proc main() : bool = {
      var m0, m1, c, b, b';
      var x, y, h, gx, gxy;

      H.init();
      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = BA.choose(gx);
      b       = ${0,1};
      h       = $uniform;
      c       = (g ^ y, h ^^ (b ? m1 : m0));
      b'      = BA.guess(c);
      return (b' = b);
    }
  }.

  local module G2 = {
    var gxy : group

    proc main() : bool = {
      var m0, m1, c, b, b';
      var x, y, h, gx;

      H.init();
      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = BA.choose(gx);
      b       = ${0,1};
      h       = $uniform;
      c       = (g ^ y, h ^^ (b ? m1 : m0));
      b'      = BA.guess(c);
      return mem G2.gxy Log.qs;
    }
  }.

  local module D(H:ARO): ROC.Dist(H) = {
    module A = A(H)

    var y:int
    var b:bool
    var m0, m1:plaintext

    proc a1(): group = {
      var x, gxy, gx;

      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = A.choose(gx);
      b       = ${0,1};
      return gxy;
    }

    proc a2(x:bits): bool = {
      var c, b';

      c  = (g ^ y, x ^^ (b ? m1 : m0));
      b' = A.guess(c);
      return (b' = b);
    }
  }.

  local lemma G0_D &m: Pr[G0.main() @ &m: res] = Pr[OnBound.G0(D,RO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline OnBound.G0(D,RO).D.a1 OnBound.G0(D,RO).D.a2; wp.
    conseq* (_: _ ==> ={b'} /\ b{1} = D.b{2})=> //.
    by inline H.hash; sim.
  qed.

  local lemma G1_D &m: Pr[G1.main() @ &m: res] = Pr[OnBound.G1(D,RO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline OnBound.G1(D,RO).D.a1 OnBound.G1(D,RO).D.a2; wp.
    conseq* (_: _ ==> ={b'} /\ b{1} = D.b{2})=> //.
    by inline H.hash; sim.
  qed.

  local lemma G2_D &m: Pr[G2.main() @ &m: res] = Pr[OnBound.G2(D,RO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline OnBound.G2(D,RO).D.a1 OnBound.G2(D,RO).D.a2; wp.
    conseq* (_: _ ==> ={glob Log, b'} /\ b{1} = D.b{2} /\ G2.gxy{1} = x{2})=> //.
    by inline H.hash; sim.
  qed.

  local lemma G0_G1_G2 &m:
    Pr[G0.main() @ &m: res] <= Pr[G1.main() @ &m: res] + Pr[G2.main() @ &m: res].
  proof.
    rewrite (G0_D &m) (G1_D &m) (G2_D &m).
    apply (OnBound.ROM_BadCall D _ _ &m).
      by progress; proc; auto; call (chooseL H _)=> //; auto; progress; smt. 
      by progress; proc; call (guessL H _)=> //; auto.
  qed.

  local module G1' = {
    proc main() : bool = {
      var m0, m1, c, b, b';
      var x, y, h, gx, gxy;

      H.init();
      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = BA.choose(gx);
      b       = ${0,1};
      h       = $uniform;
      c       = (g ^ y, h);
      b'      = BA.guess(c);
      return (b' = b);
    }
  }.

  local lemma G1_G1' &m: Pr[G1.main() @ &m: res] = Pr[G1'.main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    call (_: ={glob RO, glob Log}); first by sim.
    wp; rnd (fun h, h ^^ if b then m1 else m0){1}; rnd.
    call (_: ={glob RO, glob Log}); first by sim.
    by inline H.init RO.init; auto; progress; smt.
  qed.

  local lemma Pr_G1' &m: Pr[G1'.main() @ &m: res] = 1%r/2%r.
  proof.
    cut RO_o_ll:= RO_o_ll _; first smt.
    byphoare (_: true ==> res)=> //.
    proc.
    swap 7 3.
    rnd ((=) b').
    call (_: true);
      first by progress; apply (guessL O).
      by proc; sp; if=> //; wp; call (Log_o_ll RO _).
    auto.
    call (_: true);
      first by progress; apply (chooseL O).
      by proc; sp; if=> //; wp; call (Log_o_ll RO _).
    by inline H.init RO.init; auto; progress; expect 3 smt.
  qed.

  local module G2' = {
    var gxy : group
   
    proc main() : bool = {
      var m0, m1, c, b, b';
      var x, y, h, gx;

      H.init();
      x        = $[0..q-1];
      y        = $[0..q-1];
      gx       = g ^ x; 
      gxy      = gx ^ y;
      (m0,m1)  = BA.choose(gx);
      b        = ${0,1};
      h        = $uniform;
      c        = (g ^ y, h);
      b'       = BA.guess(c);
      return mem gxy Log.qs;
    }
  }.

  local lemma G2_G2' &m: Pr[G2.main() @ &m: res] = Pr[G2'.main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    call (_: ={glob RO, glob Log}); first by sim.
    wp; rnd (fun h, h ^^ if b then m1 else m0){1}; rnd.
    call (_: ={glob RO, glob Log}); first by sim.
    by inline H.init RO.init; auto; progress; smt.
  qed.

  local equiv G2'_SCDH: G2'.main ~ SCDH(SCDH_from_CPA(A,RO)).main:
    ={glob A} ==> res{1} = res{2} /\ card Log.qs{1} <= qH.
  proof.
    proc.
    inline SCDH_from_CPA(A,RO).solve.
    swap{2} 5 -4; swap{1} 7 3.
    rnd{1}; wp.
    seq  8  7: (={glob BA} /\
                c{1} = (gy, h){2} /\
                G2'.gxy{1} = g ^ (x * y){2} /\
                card Log.qs{1} <= qH).
      wp; rnd; call (_: ={glob H} /\ card Log.qs{1} <= qH).
        by proc; sp; if=> //; inline Bound(RO).LO.o RO.o; auto; smt.
      by inline H.init RO.init; auto; progress; smt.
    call (_: ={glob H} /\ card Log.qs{1} <= qH).
      by proc; sp; if=> //; inline Bound(RO).LO.o RO.o; auto; smt.
    by skip; smt.
  qed.
      
  local lemma Pr_G2'_SCDH &m : 
    Pr[G2'.main() @ &m: res]
    = Pr[SCDH(SCDH_from_CPA(A,RO)).main() @ &m : res]
  by byequiv G2'_SCDH.
   
  local lemma Reduction &m :
    Pr[CPA(S,BA).main() @ &m : res] <=
    1%r / 2%r + Pr[SCDH(SCDH_from_CPA(A,RO)).main() @ &m : res].
  proof. 
    rewrite (Pr_CPA_G0 &m).
    rewrite -(Pr_G1' &m) -(G1_G1' &m).
    rewrite -(Pr_G2'_SCDH &m) -(G2_G2' &m).
    by apply (G0_G1_G2 &m).
  qed.

  lemma mult_inv_le_r (x y z:real) : 
    0%r < x => (1%r / x) * y <= z => y <= x * z.
  proof.
    move=> lt0x ledivxyz.
    print theory Real.
    cut:= mulrMle (1%r / x * y) z x _ _; [by smt | done  |].
    by rewrite -Real.Comm.Comm -Real.Assoc.Assoc -div_def 2:mul_div // smt.
  qed.    

  (** Composing reduction from CPA to SCDH with reduction from SCDH to CDH *)
  lemma Security &m:
      Pr[CPA(S,A(Bound(RO))).main() @ &m: res] - 1%r / 2%r <= 
      qH%r * Pr[CDH.CDH(CDH_from_SCDH(SCDH_from_CPA(A,RO))).main() @ &m: res].
  proof.
    apply (Trans _ (Pr[SCDH(SCDH_from_CPA(A,RO)).main() @ &m: res]));
      first smt.
    apply mult_inv_le_r; first smt.
    by apply (Top.SCDH.Reduction (SCDH_from_CPA(A,RO)) &m); apply qH_pos.
  qed.
end section.

print axiom Security.
