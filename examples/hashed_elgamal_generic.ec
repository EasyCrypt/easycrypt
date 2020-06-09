require import AllCore Int Real FSet StdOrder.
require (*--*) BitWord Distr DInterval.
(*---*) import RealOrder RField.
require (*--*) DiffieHellman ROM PKE_CPA.

(* The type of plaintexts: bitstrings of length k *)
op k: { int | 0 < k } as gt0_k.

clone import BitWord as Bits with
  op n <- k
proof gt0_n by exact/gt0_k
rename
  "word" as "bits"
  "dunifin" as "dbits".
import DWord.

(* Upper bound on the number of calls to H *)
op qH: { int | 0 < qH } as gt0_qH.

(* Assumption: Set CDH *)
clone import DiffieHellman.Set_CDH as SCDH with
  op n <- qH.
import DiffieHellman G FDistr.

type pkey = group.
type skey = t.
type ptxt = bits.
type ctxt = group * bits.

(* Goal: PK IND-CPA *)
clone import PKE_CPA as PKE with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- ctxt.

(* Some abstract hash oracle *)
module type Hash = {
  proc init(): unit
  proc hash(x:group): bits
}.

module Hashed_ElGamal (H:Hash): Scheme = {
  proc kg(): pkey * skey = {
    var sk;

    H.init();
    sk <$ dt;
    return (g ^ sk, sk);
  }

  proc enc(pk:pkey, m:ptxt): ctxt = {
    var y, h;

    y <$ dt;
    h <@ H.hash(pk ^ y);
    return (g ^ y, h +^ m);
  }

  proc dec(sk:skey, c:ctxt): ptxt option = {
    var gy, h, hm;

    (gy, hm) <- c;
    h        <@ H.hash(gy ^ sk);
    return Some (h +^ hm);
  }
}.

clone import ROM.ROM_BadCall as ROC with
  type from  <- group,
  type to    <- bits,
  op dsample <- fun (x:group), dbits,
  op qH      <- qH
proof * by exact/dbits_ll.

(* Adversary Definitions *)
module type Adversary (O:ARO) = {
  proc choose(pk:pkey): ptxt * ptxt
  proc guess(c:ctxt)  : bool
}.

(* Specializing and merging the hash function *)
module H:Hash = {
  proc init(): unit = { RO.init(); Log.qs <- fset0; }
  proc hash(x:group): bits = { var y; y <@ RO.o(x); return y; }
}.

(* The initial scheme *)
module S = Hashed_ElGamal(H).

(* The reduction *)
module SCDH_from_CPA(A:Adversary,O:Oracle): Top.SCDH.Adversary = {
  module BA = A(Bound(O))

  proc solve(gx:group, gy:group): group fset = {
    var m0, m1, h, b';

    H.init();
    (m0,m1)  <@ BA.choose(gx);
    h        <$ dbits;
    b'       <@ BA.guess(gy, h);
    return Log.qs;
  }
}.

(* We want to bound the probability of A winning CPA(Bounder(A,RO),S) in terms of
   the probability of B = CDH_from_CPA(SCDH_from_CPA(A,RO)) winning CDH(B) *)
section.
  declare module A: Adversary {RO, Log, OnBound.G1, OnBound.G2}.

  axiom choose_ll (O <: ARO {A}): islossless O.o => islossless A(O).choose.
  axiom guess_ll (O <: ARO {A}) : islossless O.o => islossless A(O).guess.

  local module BA = A(Bound(RO)).

  local module G0 = {
    var gxy:group

    proc main(): bool = {
      var m0, m1, c, b, b';
      var x, y, h, gx;

      H.init();
      x       <$ dt;
      y       <$ dt;
      gx      <- g ^ x;
      gxy     <- gx ^ y;
      (m0,m1) <@ BA.choose(gx);
      b       <$ {0,1};
      h       <@ H.hash(gxy);
      c       <- (g ^ y, h +^ (b ? m1 : m0));
      b'      <@ BA.guess(c);
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
      x       <$ dt;
      y       <$ dt;
      gx      <- g ^ x;
      gxy     <- gx ^ y;
      (m0,m1) <@ BA.choose(gx);
      b       <$ {0,1};
      h       <$ dbits;
      c       <- (g ^ y, h +^ (b ? m1 : m0));
      b'      <@ BA.guess(c);
      return (b' = b);
    }
  }.

  local module G2 = {
    var gxy : group

    proc main() : bool = {
      var m0, m1, c, b, b';
      var x, y, h, gx;

      H.init();
      x       <$ dt;
      y       <$ dt;
      gx      <- g ^ x;
      gxy     <- gx ^ y;
      (m0,m1) <@ BA.choose(gx);
      b       <$ {0,1};
      h       <$ dbits;
      c       <- (g ^ y, h +^ (b ? m1 : m0));
      b'      <@ BA.guess(c);
      return G2.gxy \in Log.qs;
    }
  }.

  local module (D : ROC.Dist) (H : ARO) = {
    module A = A(H)

    var y:t
    var b:bool
    var m0, m1:ptxt

    proc a1(): group = {
      var x, gxy, gx;

      x       <$ dt;
      y       <$ dt;
      gx      <- g ^ x;
      gxy     <- gx ^ y;
      (m0,m1) <@ A.choose(gx);
      b       <$ {0,1};
      return gxy;
    }

    proc a2(x:bits): bool = {
      var c, b';

      c  <- (g ^ y, x +^ (b ? m1 : m0));
      b' <@ A.guess(c);
      return (b' = b);
    }
  }.

  local lemma G0_D &m: Pr[G0.main() @ &m: res] = Pr[OnBound.G0(D,RO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline OnBound.G0(D,RO).D.a1 OnBound.G0(D,RO).D.a2; wp.
    conseq (_: _ ==> ={b'} /\ b{1} = D.b{2})=> //.
    by inline H.hash; sim.
  qed.

  local lemma G1_D &m: Pr[G1.main() @ &m: res] = Pr[OnBound.G1(D,RO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline OnBound.G1(D,RO).D.a1 OnBound.G1(D,RO).D.a2; wp.
    conseq (_: _ ==> ={b'} /\ b{1} = D.b{2})=> //.
    by inline H.hash; sim.
  qed.

  local lemma G2_D &m: Pr[G2.main() @ &m: res] = Pr[OnBound.G2(D,RO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline OnBound.G2(D,RO).D.a1 OnBound.G2(D,RO).D.a2; wp.
    conseq (_: _ ==> ={glob Log, b'} /\ b{1} = D.b{2} /\ G2.gxy{1} = x{2})=> //.
    by inline H.hash; sim.
  qed.

  local lemma G0_G1_G2 &m:
    Pr[G0.main() @ &m: res] <= Pr[G1.main() @ &m: res] + Pr[G2.main() @ &m: res].
  proof.
    rewrite (G0_D &m) (G1_D &m) (G2_D &m).
    apply (OnBound.ROM_BadCall D _ _ &m).
    + move=> H0 H0_o_ll; proc; auto; call (choose_ll H0 _)=> //; auto=> />.
      smt(dt_ll DBool.dbool_ll).
    by progress; proc; call (guess_ll H _)=> //; auto.
  qed.

  local module G1' = {
    proc main() : bool = {
      var m0, m1, c, b, b';
      var x, y, h, gx, gxy;

      H.init();
      x       <$ dt;
      y       <$ dt;
      gx      <- g ^ x;
      gxy     <- gx ^ y;
      (m0,m1) <@ BA.choose(gx);
      b       <$ {0,1};
      h       <$ dbits;
      c       <- (g ^ y, h);
      b'      <@ BA.guess(c);
      return (b' = b);
    }
  }.

  local lemma G1_G1' &m: Pr[G1.main() @ &m: res] = Pr[G1'.main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    call (_: ={glob RO, glob Log}); first by sim.
    wp; rnd (fun h, h +^ if b then m1 else m0){1}; rnd.
    call (_: ={glob RO, glob Log}); first by sim.
    by inline H.init RO.init; auto=> /> *; split => *; algebra.
  qed.

  local lemma Pr_G1' &m: Pr[G1'.main() @ &m: res] = 1%r/2%r.
  proof.
    cut RO_o_ll:= RO_o_ll _; first by smt(dbits_ll).
    byphoare (_: true ==> res)=> //.
    proc.
    swap 7 3.
    rnd (pred1 b').
    conseq (_: true) => />.
    + by move=> b'; rewrite DBool.dbool1E /pred1 => />.
    islossless.
    + by apply (guess_ll (Bound(RO))); islossless.
    by apply (choose_ll (Bound(RO))); islossless.
  qed.

  local module G2' = {
    var gxy : group

    proc main() : bool = {
      var m0, m1, c, b, b';
      var x, y, h, gx;

      H.init();
      x        <$ dt;
      y        <$ dt;
      gx       <- g ^ x;
      gxy      <- gx ^ y;
      (m0,m1)  <@ BA.choose(gx);
      b        <$ {0,1};
      h        <$ dbits;
      c        <- (g ^ y, h);
      b'       <@ BA.guess(c);
      return gxy \in Log.qs;
    }
  }.

  local lemma G2_G2' &m: Pr[G2.main() @ &m: res] = Pr[G2'.main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    call (_: ={glob RO, glob Log}); first by sim.
    wp; rnd (fun h, h +^ if b then m1 else m0){1}; rnd.
    call (_: ={glob RO, glob Log}); first by sim.
    by inline H.init RO.init; auto=> /> *; split => *; algebra.
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
        proc; sp; if=> //; inline Bound(RO).LO.o RO.o; auto=> />.
        by move=> &2 _ szqs_lt_qH _ _; rewrite fcardU fcard1; smt(fcard_ge0).
      by inline H.init RO.init; auto=> />; rewrite fcards0; smt(gt0_qH pow_pow).
    call (_: ={glob H} /\ card Log.qs{1} <= qH).
      proc; sp; if=> //; inline Bound(RO).LO.o RO.o; auto=> /> &2 _ szqs_lt_qH _ _.
      by rewrite fcardU fcard1; smt(fcard_ge0).
    by auto => />.
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

  (** Composing reduction from CPA to SCDH with reduction from SCDH to CDH *)
  lemma Security &m:
      Pr[CPA(S,A(Bound(RO))).main() @ &m: res] - 1%r / 2%r <=
      qH%r * Pr[CDH.CDH(CDH_from_SCDH(SCDH_from_CPA(A,RO))).main() @ &m: res].
  proof.
    apply (ler_trans (Pr[SCDH(SCDH_from_CPA(A,RO)).main() @ &m: res])).
    + smt(Reduction).
    have:= Self.SCDH.Reduction (SCDH_from_CPA(A,RO)) &m gt0_qH.    
    by rewrite -mulrA mul1r mulrC ler_pdivr_mulr 1:lt_fromint 1:gt0_qH mulrC.
  qed.
end section.

print axiom Security.
