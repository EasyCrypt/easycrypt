require import Pred.
require import Distr.
require import Int.
require import Real.
require import FMap. 
require import FSet.
require import CDH.
require (*--*) AWord.
require (*--*) ROM.
require (*--*) PKE.

(** We extend the basic lazy random oracle with a generic argument
    replacing a single oracle call in the middle of an experiment
    with a random sampling. The probability of distinguishing the
    two is bounded by the probability that another query in the
    experiment collides with the one we singled out. Ideally, this
    should be pushed into either the ROM library, or into a
    ProveIt-specific context.                                       *)
theory ROM_Call.
  type from.
  type to.

  op dsample: from -> to distr.
  axiom dsampleL x: mu (dsample x) True = 1%r.

  op qH:int.
  axiom qH_pos: 0 < qH.

  clone import ROM.Lazy as ROM with
    type from  <- from,
    type to    <- to,
    op dsample <- dsample.

  module type Dist(H:Types.ARO) = {
    proc a1(): from
    proc a2(x:to): bool
  }.

  module ARO(O:Types.ARO) = {
    var qs:from set

    proc o(x:from): to = {
      var r = witness;

      if (card qs < qH) {
        r  = O.o(x);
        qs = add x qs;
      }
      return r;
    }
  }.

  module Bounder(D:Dist,O:Types.ARO) = {
    module D' = D(ARO(O))

    proc a1 = D'.a1
    proc a2 = D'.a2
  }.

  module G0(D:Dist, H:Types.Oracle) = {
    module D = Bounder(D,H)

    proc main(): bool = {
      var x, y, b;

      H.init();
      ARO.qs = FSet.empty;
      x = D.a1();
      y = H.o(x);
      b = D.a2(y);
      return b;
    }
  }.

  module G1(D:Dist, H:Types.Oracle) = {
    module D = Bounder(D,H)

    var x:from

    proc main(): bool = {
      var y, b;

      H.init();
      ARO.qs = FSet.empty;
      x = D.a1();
      y = $dsample x;
      b = D.a2(y);
      return b;
    }
  }.

  module G2(D:Dist, H:Types.Oracle) = {
    module D = Bounder(D,H)

    var x:from

    proc main(): bool = {
      var y, b;

      H.init();
      ARO.qs = FSet.empty;
      x = D.a1();
      y = $dsample x;
      b = D.a2(y);
      return mem x ARO.qs;
    }
  }.

  lemma Abstract_Bad (D <: Dist {Bounder, RO, G1, G2}) &m:
    (forall (H <: Types.ARO {D}), islossless H.o => islossless D(H).a1) =>
    (forall (H <: Types.ARO {D}), islossless H.o => islossless D(H).a2) =>
    Pr[G0(D,RO).main() @ &m: res]
    <= Pr[G1(D,RO).main() @ &m: res]
     + Pr[G2(D,RO).main() @ &m: res].
  proof.
    move=> Da1L Da2L.
    cut ->: Pr[G2(D,RO).main() @ &m: res] = Pr[G1(D,RO).main() @ &m: mem G1.x ARO.qs].
      byequiv (_: ={glob D} ==> res{1} = (mem G1.x ARO.qs){2})=> //.
      proc.
      call (_: ={glob ARO, glob RO}); first by sim.
      rnd; call (_: ={glob ARO, glob RO}); first by sim.
      by inline *; wp.
    cut: Pr[G0(D,RO).main() @ &m: res] <= Pr[G1(D,RO).main() @ &m: res \/ mem G1.x ARO.qs].
      byequiv (_: ={glob D} ==> !mem G1.x{2} ARO.qs{2} => ={res})=> //; last smt.
      proc.
      call (_: !mem G1.x{2} ARO.qs{2} =>
               ={glob D, ARO.qs, x} /\
               ARO.qs{2} = dom RO.m{2} /\
               eq_except RO.m{1} RO.m{2} G1.x{2} ==>
               !mem G1.x{2} ARO.qs{2} =>
               ={ARO.qs, res} /\
               ARO.qs{2} = dom RO.m{2} /\
               eq_except RO.m{1} RO.m{2} G1.x{2}).
        proc (mem G1.x ARO.qs)
             (={ARO.qs} /\
              ARO.qs{2} = dom RO.m{2} /\
              eq_except RO.m{1} RO.m{2} G1.x{2})=> //;
          first 2 smt.
          proc; sp; if=> //; inline RO.o; auto; progress; first 5 last; last 7 smt.
          case (x{2} = G1.x{2}); first smt.
          by move=> neq; cut:= H0; rewrite eq_except_def; smt.
          smt.
          smt.
          case (x{2} = G1.x{2}); first smt.
          by move=> neq; cut:= H0; rewrite eq_except_def; smt.
        by progress; proc; sp; if=> //; wp; call (lossless_o _); first smt.
        by progress; proc; sp; if=> //; wp; call (lossless_o _); [smt | skip; smt].
      inline RO.o; wp; rnd; wp.
      call (_: ={glob ARO, glob RO} /\ ARO.qs{2} = dom RO.m{2}).
        by proc; sp; if=> //; inline RO.o; auto; progress; smt.
      by inline RO.init; auto; progress; expect 7 smt.
    by rewrite Pr [mu_or]; smt.
  qed.
end ROM_Call.

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
clone Set_CDH as SCDH with
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

clone import ROM_Call as ROC with
  type from  <- group,
  type to    <- bits,
  op dsample <- fun (x:group), uniform,
  op qH      <- qH
proof * by smt.

import ROM.
import Types.

(* Adversary Definitions *)
module type Adversary (O:ARO) = {
  proc choose(pk:pkey)    : plaintext * plaintext
  proc guess(c:ciphertext): bool
}.

module Bounder'(A:Adversary,O:ARO) = {
  module A' = A(ARO(O))

  proc choose = A'.choose
  proc guess  = A'.guess
}.

(* Specializing and merging the hash function *)
module H:Hash = {
  proc init(): unit = { RO.init(); ARO.qs = FSet.empty; }
  proc hash(x:group): bits = { var y; y = RO.o(x); return y; }
}.

(* The initial scheme *)
module S = Hashed_ElGamal(H).

(* Correctness result *)
hoare Correctness: Correctness(S).main: true ==> res.
proof. by proc; inline *; auto; progress; smt. qed.

(* The reduction *)
module SCDH_from_CPA(A:Adversary,O:ARO): SCDH.Adversary = {
  module BA = Bounder'(A,O)

  proc solve(gx:group, gy:group): group set = {
    var m0, m1, h, b';

    H.init();
    (m0,m1)  = BA.choose(gx);
    h        = $uniform;
    b'       = BA.guess(gy, h);
    return ARO.qs;
  }
}.

(* We want to bound the probability of A winning CPA(Bounder(A,RO),S) in terms of
   the probability of B = CDH_from_CPA(SCDH_from_CPA(A,RO)) winning CDH(B) *)
section.
  declare module A: Adversary {RO, Bounder, ROC.G1, ROC.G2}.

  axiom chooseL (O <: ARO {A}): islossless O.o => islossless A(O).choose.
  axiom guessL (O <: ARO {A}) : islossless O.o => islossless A(O).guess.

  local module BA = Bounder'(A,RO).

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
    call (_: ={glob H, ARO.qs}); first by sim.
    wp; call (_: ={glob H}); first by sim.
    wp; rnd.
    call (_: ={glob H, ARO.qs}); first by sim.
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
      return mem G2.gxy ARO.qs;
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

  local lemma G0_D &m: Pr[G0.main() @ &m: res] = Pr[ROC.G0(D,RO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline ROC.G0(D,RO).D.a1 ROC.G0(D,RO).D.a2; wp.
    conseq* (_: _ ==> ={b'} /\ b{1} = D.b{2})=> //.
    by inline H.hash H.init; sim.
  qed.

  local lemma G1_D &m: Pr[G1.main() @ &m: res] = Pr[ROC.G1(D,RO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline ROC.G1(D,RO).D.a1 ROC.G1(D,RO).D.a2; wp.
    conseq* (_: _ ==> ={b'} /\ b{1} = D.b{2})=> //.
    by inline H.hash H.init; sim.
  qed.

  local lemma G2_D &m: Pr[G2.main() @ &m: res] = Pr[ROC.G2(D,RO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline ROC.G2(D,RO).D.a1 ROC.G2(D,RO).D.a2; wp.
    conseq* (_: _ ==> ={glob ARO, b'} /\ b{1} = D.b{2} /\ G2.gxy{1} = ROC.G2.x{2})=> //.
    by inline H.hash H.init; sim.
  qed.

  local lemma G0_G1_G2 &m:
    Pr[G0.main() @ &m: res] <= Pr[G1.main() @ &m: res] + Pr[G2.main() @ &m: res].
  proof.
    rewrite (G0_D &m) (G1_D &m) (G2_D &m).
    apply (Abstract_Bad D &m).
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
    call (_: ={glob RO, glob ARO}); first by sim.
    wp; rnd (fun h, h ^^ if b then m1 else m0){1}; rnd.
    call (_: ={glob RO, glob ARO}); first by sim.
    by inline H.init RO.init; auto; progress; smt.
  qed.

  local lemma Pr_G1' &m: Pr[G1'.main() @ &m: res] = 1%r/2%r.
  proof.
    byphoare (_: true ==> res)=> //.
    proc.
    swap 7 3.
    rnd ((=) b').
    call (_: true);
      first by progress; apply (guessL O).
      by proc; sp; if=> //; wp; call (lossless_o _); first smt.
    auto.
    call (_: true);
      first by progress; apply (chooseL O).
      by proc; sp; if=> //; wp; call (lossless_o _); first smt.
    inline H.init RO.init; auto; progress; expect 3 smt.
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
      return mem gxy ARO.qs;
    }
  }.

  local lemma G2_G2' &m: Pr[G2.main() @ &m: res] = Pr[G2'.main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    call (_: ={glob RO, glob ARO}); first by sim.
    wp; rnd (fun h, h ^^ if b then m1 else m0){1}; rnd.
    call (_: ={glob RO, glob ARO}); first by sim.
    by inline H.init RO.init; auto; progress; smt.
  qed.

  local equiv G2'_SCDH: G2'.main ~ SCDH.SCDH(SCDH_from_CPA(A,RO)).main:
    ={glob A} ==> res{1} = res{2} /\ card ARO.qs{1} <= qH.
  proof.
    proc.
    inline SCDH_from_CPA(A,RO).solve.
    swap{2} 5 -4; swap{1} 7 3.
    rnd{1}; wp.
    seq  8  7: (={glob BA} /\
                c{1} = (gy, h){2} /\
                G2'.gxy{1} = g ^ (x * y){2} /\
                card ARO.qs{1} <= qH).
      wp; rnd; call (_: ={glob H} /\ card ARO.qs{1} <= qH).
        by proc; sp; if=> //; inline RO.o; auto; smt.
      by inline H.init RO.init; auto; progress; smt.
    call (_: ={glob H} /\ card ARO.qs{1} <= qH).
      by proc; sp; if=> //; inline RO.o; auto; smt.
    by skip; smt.
  qed.
      
  local lemma Pr_G2'_SCDH &m : 
    Pr[G2'.main() @ &m: res]
    = Pr[SCDH.SCDH(SCDH_from_CPA(A,RO)).main() @ &m : res]
  by byequiv G2'_SCDH.
   
  local lemma Reduction &m :
    Pr[CPA(S,BA).main() @ &m : res] <=
    1%r / 2%r + Pr[SCDH.SCDH(SCDH_from_CPA(A,RO)).main() @ &m : res].
  proof. 
    rewrite (Pr_CPA_G0 &m).
    rewrite -(Pr_G1' &m) -(G1_G1' &m).
    rewrite -(Pr_G2'_SCDH &m) -(G2_G2' &m).
    by apply (G0_G1_G2 &m).
  qed.

  lemma mult_inv_le_r (x y z:real) : 
    0%r < x => (1%r / x) * y <= z => y <= x * z
  by [].

  (** Composing reduction from CPA to SCDH with reduction from SCDH to CDH *)
  lemma Security &m :
      Pr[CPA(S,Bounder'(A,RO)).main() @ &m: res] - 1%r / 2%r <= 
      qH%r * Pr[CDH.CDH(SCDH.CDH_from_SCDH(SCDH_from_CPA(A,RO))).main() @ &m: res].
  proof.
    apply (Trans _ (Pr[SCDH.SCDH(SCDH_from_CPA(A,RO)).main() @ &m: res]));
      first smt.
    apply mult_inv_le_r; first smt.
    by apply (SCDH.Reduction (SCDH_from_CPA(A,RO)) &m); smt.
  qed.
end section.

print axiom Security.
