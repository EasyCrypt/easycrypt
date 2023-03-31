require import Int Real SmtMap FSet StdOrder.
(*---*) import RealOrder.

require (*--*) DiffieHellman.
require (*--*) BitWord.
require (*--*) ROM.
require (*--*) PKE.

clone import BitWord as Bitstring.

type bitstring = bool List.list.

(** Upper bound on the number of calls to H **)
op qH: int.
axiom qH_pos: 0 < qH.

(** Assumption: set CDH with n = qH **)
clone DiffieHellman as DH
  with op Set_CDH.n <- qH.
import DH.CDH DH.G DH.GP DH.FD DH.GP.ZModE.
import DH.Set_CDH.

(** Assumption: a ROM (lazy) **)
module type Hash = {
  proc init(): unit
  proc hash(x:group): word
}.

clone import ROM as ROG with
  type in_t  <- group,
  type out_t <- word,
  op   dout  <- (fun _ => Distr.MUniform.duniform (Finite.to_seq<:word> predT)).

clone import ROG.Lazy as RandOrcl_group.

(** Construction: a PKE **)
type pkey       = group.
type skey       = exp.
type plaintext  = word.
type ciphertext = group * word.

clone import PKE as PKE_ with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

(** Concrete Construction: Hashed ElGammal **)
module Hashed_ElGamal (H : Hash) : Scheme = {
  proc kg(): pkey * skey = {
    var sk;

    H.init();
    sk <$ dt;
    return (g ^ sk, sk);
  }

  proc enc(pk:pkey, m:plaintext): ciphertext = {
    var y, h;

    y <$ dt;
    h <@ H.hash(pk ^ y);
    return (g ^ y, h +^ m);
  }

  proc dec(sk:skey, c:ciphertext): plaintext option = {
    var gy, h, hm;

    (gy, hm) <- c;
    h        <@ H.hash(gy ^ sk);
    return Some (h +^ hm);
  }
}.

(** Adversary Definitions **)
module type Adversary (O : POracle) = {
  proc choose(pk:pkey)    : plaintext * plaintext
  proc guess(c:ciphertext): bool
}.

(* We give the adversary access to a version of the ROM that stops
   answering past a certain number of queries *)
(* TODO: use generic defs from ROM.ec *)
module Bounder (A : Adversary, O : POracle) = {
  module POracle = {
    var qs : group fset

    proc o (x : group): word = {
      var r <- witness;

      if (card qs < qH) {
        r  <@ O.o(x);
        qs <- qs `|` fset1 x;
      }
      return r;
    }
  }

  module A' = A(POracle)

  proc choose = A'.choose
  proc guess  = A'.guess
}.

(* Specializing the hash function and merging it into the bounding wrapper *)
module H:Hash = {
  proc init(): unit = { LRO.init(); Bounder.POracle.qs <- fset0; }
  proc hash = LRO.o
}.

(* The initial scheme: Our construction applied to the ROM H *)
module S = Hashed_ElGamal(H).

(** Correctness **)
hoare Correctness: Correctness(S).main: true ==> res.
proof.
  proc; inline*; auto => /= &hr sk0 Hsk0 y Hy y0 Hy0.
  rewrite mem_empty mem_set /= -!expM.
  rewrite DH.GP.ZModE.ZModpField.mulrC get_set_sameE /= => y1 _.
  algebra.
qed.

(** Security **)
(* Reduction *)
module SCDH_from_CPA (A : Adversary, O : POracle): DH.Set_CDH.Adversary = {
  module BA = Bounder(A, O)

  proc solve(gx:group, gy:group): group fset = {
    var m0, m1, h, b';

    H.init();
    (m0,m1)  <@ BA.choose(gx);
    h        <$ DWord.dunifin;
    b'       <@ BA.guess(gy, h);
    return Bounder.POracle.qs;
  }
}.

(* We want to bound the probability of A winning CPA(Bounder(A,RO),S) in terms of
   the probability of B = CDH_from_SCDH(SCDH_from_CPA(A,RO)) winning CDH(B) *)
section.
  declare module A <: Adversary {-LRO, -Bounder}.

  axiom chooseL (O <: POracle {-A}): islossless O.o => islossless A(O).choose.
  axiom guessL (O <: POracle {-A}) : islossless O.o => islossless A(O).guess.

  local module BA = Bounder(A,LRO).

  (* Inline the challenge encryption *)
  local module G0 = {
    var gxy : group

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
    call (_: ={glob H, Bounder.POracle.qs}); first by sim.
    wp; call (_: ={glob H}); first by sim.
    wp; rnd.
    call (_: ={glob H, Bounder.POracle.qs}); first by sim.
    wp; do !rnd.
    by call (_: true ==> ={glob H}); first by sim.
  qed.

  local lemma Pr_CPA_G0 &m:
    Pr[CPA(S,BA).main() @ &m: res] = Pr[G0.main() @ &m: res]
  by byequiv CPA_G0.

  (* Replace the challenge hash with a random sampling *)
  local module G1 = {
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
      h       <$ DWord.dunifin;
      c       <- (g ^ y, h +^ (b ? m1 : m0));
      b'      <@ BA.guess(c);
      return (b' = b);
    }
  }.

  (* The equivalence is up to the adversary guessing the challenge *)
  local equiv G0_G1:
    G0.main ~ G1.main: ={glob A} ==> !(mem Bounder.POracle.qs G1.gxy){2} => ={res}.
  proof.
    proc.
    (* Up until the hash call, the two games are equivalent *)
    seq  7  7: (={glob BA, x, y, b, m0, m1} /\ G0.gxy{1} = G1.gxy{2} /\
                (Bounder.POracle.qs = fdom LRO.m){2}).
      rnd; call (_: ={glob Bounder, glob H} /\
                    (Bounder.POracle.qs = fdom LRO.m){2}).
        proc; sp; if=> //; inline LRO.o; wp; rnd; wp; skip => /> *.
        rewrite fdom_set /= => ?; rewrite fsetP => y.
        rewrite in_fsetU1; smt(mem_fdom).
      by inline H.init LRO.init; wp; do !rnd; wp; skip; smt.
    (* After that, the equivalence relation may be broken if the adversary queries g^(x*y) from the ROM *)
    (* BUG: the invariant form of call raises an anomaly *)
    call (_: (!mem Bounder.POracle.qs G1.gxy){2} =>
             ={glob A, Bounder.POracle.qs, c} /\
             eq_except (pred1 G1.gxy{2}) LRO.m{1} LRO.m{2}
             ==>
             (!mem Bounder.POracle.qs G1.gxy){2} =>
             ={glob A, Bounder.POracle.qs, res} /\
             eq_except (pred1 G1.gxy{2}) LRO.m{1} LRO.m{2})=> //.
      proc (mem Bounder.POracle.qs G1.gxy) (={Bounder.POracle.qs} /\
                                            eq_except (pred1 G1.gxy{2}) LRO.m{1} LRO.m{2}) => //.
        by move=> &1 &2 H /H.
        by move=> &1 &2 H /H.
        exact guessL.
        proc; sp; if=> //; inline *; auto => /> *.
        rewrite !get_set_sameE in_fsetU1 /=; split => *; 1: by smt.
        by smt(eq_exceptP).
        by move=> &2 bad; proc; sp; if=> //; wp; call (LRO_o_ll _); first smt.
        by move=> &1; proc; sp; if=> //; wp; call (LRO_o_ll _); [ | skip]; smt.
    inline H.hash LRO.o; auto => /> *; split => *; 1: by smt.
    by rewrite !get_set_sameE; smt.
  qed.

  local lemma Pr_G0_G1 &m:
    Pr[G0.main() @ &m: res] <= Pr[G1.main() @ &m: res] +
                               Pr[G1.main() @ &m: mem Bounder.POracle.qs G1.gxy].
  proof.
    have: Pr[G0.main() @ &m: res] <= Pr[G1.main() @ &m: res \/ mem Bounder.POracle.qs G1.gxy].
      by byequiv G0_G1=> //; smt.
    by rewrite Pr [mu_or]; smt.
  qed.

  (* Make it clear that the result is independent from the adversary's message *)
  local module G2 = {
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
      h        <$ DWord.dunifin;
      c        <- (g ^ y, h);
      b'       <@ BA.guess(c);
      b        <$ {0,1};
      return (b' = b);
    }
  }.

  local equiv G1_G2:
     G1.main ~ G2.main: ={glob A} ==> ={res, Bounder.POracle.qs} /\ G1.gxy{1} = G2.gxy{2}.
  proof.
    proc.
    swap{2} 10 -3.
    call (_: ={glob H} /\ G1.gxy{1} = G2.gxy{2});
      first by sim.
    wp.
    rnd (fun h, h +^ if b then m1 else m0){1}; rnd.
    call (_: ={glob H} /\ G1.gxy{1} = G2.gxy{2}).
      by sim.
    by inline H.init LRO.init; auto; progress; algebra.
  qed.

  local lemma Pr_G1_G2_res &m:
    Pr[G1.main() @ &m: res] = Pr[G2.main() @ &m: res]
  by byequiv G1_G2.

  local lemma Pr_G1_G2_coll &m:
    Pr[G1.main() @ &m: mem Bounder.POracle.qs G1.gxy] =
    Pr[G2.main() @ &m: mem Bounder.POracle.qs G2.gxy]
  by byequiv G1_G2.

  (* G2 is clearly uniform random *)
  local lemma Pr_G2 &m: Pr[G2.main() @ &m: res] = 1%r / 2%r.
  proof.
    byphoare (_: true ==> _)=> //.
    proc; rnd ((=) b')=> //=.
    conseq (_: _ ==> true); first smt.
    call (_: true)=> //=.
      by apply guessL.
      by proc; sp; if=> //; wp; call (LRO_o_ll _); first smt.
    wp; rnd; call (_ : true)=> //=.
      by apply chooseL.
      by proc; sp; if=> //; wp; call (LRO_o_ll _); first smt.
    by inline H.init LRO.init; auto; smt.
  qed.

  (** Final reduction **)
  (* We add the bound on the number of ROM queries answered to facilitate the computation later on *)
  local equiv G2_SCDH: G2.main ~ SCDH(SCDH_from_CPA(A,LRO)).main:
    ={glob A} ==> (mem Bounder.POracle.qs G2.gxy){1} = res{2} /\ card Bounder.POracle.qs{1} <= qH.
  proof.
    proc.
    inline SCDH_from_CPA(A,LRO).solve.
    swap{2} 5 -4.
    rnd{1}; wp.
    seq  8  7: (={glob BA} /\
                c{1} = (gy, h){2} /\
                G2.gxy{1} = g ^ (x * y){2} /\
                card Bounder.POracle.qs{1} <= qH).
      wp; rnd; call (_: ={glob H} /\ card Bounder.POracle.qs{1} <= qH).
        by proc; sp; if=> //; inline LRO.o; auto; smt.
      by inline H.init LRO.init; auto; smt.
    call (_: ={glob H} /\ card Bounder.POracle.qs{1} <= qH).
      by proc; sp; if=> //; inline LRO.o; auto; smt.
    by skip; smt.
  qed.

  local lemma Pr_G2_SCDH &m :
    Pr[G2.main() @ &m : mem Bounder.POracle.qs G2.gxy]
    = Pr[SCDH(SCDH_from_CPA(A,LRO)).main() @ &m : res]
  by byequiv G2_SCDH.

  local lemma Reduction &m :
    Pr[CPA(S,BA).main() @ &m : res] <=
    1%r / 2%r + Pr[SCDH(SCDH_from_CPA(A,LRO)).main() @ &m : res].
  proof.
    rewrite (Pr_CPA_G0 &m).
    apply (ler_trans (Pr[G1.main() @ &m : res] + Pr[G1.main() @ &m: mem Bounder.POracle.qs G1.gxy]));
      first by apply (Pr_G0_G1 &m).
    by rewrite (Pr_G1_G2_res &m) (Pr_G2 &m) (Pr_G1_G2_coll &m) (Pr_G2_SCDH &m).
  qed.

  (** Composing reduction from CPA to SCDH with reduction from SCDH to CDH *)
  lemma Security &m :
      Pr[CPA(S,Bounder(A,LRO)).main() @ &m: res] - 1%r / 2%r <=
      qH%r * Pr[CDH(CDH_from_SCDH(SCDH_from_CPA(A,LRO))).main() @ &m: res].
  proof.
    apply (ler_trans (Pr[SCDH(SCDH_from_CPA(A,LRO)).main() @ &m: res]));
      first smt.
    apply/ler_pdivr_mull; 1: smt.
    by rewrite (DH.Set_CDH.Reduction (SCDH_from_CPA(A,LRO)) &m); smt.
  qed.
end section.

print axiom Security.
