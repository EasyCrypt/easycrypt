<<<<<<< HEAD
require import AllCore FSet List SmtMap CHoareTactic.
require (*--*) BitWord Distr DInterval.
(*---*) import StdOrder.RealOrder StdRing.RField StdBigop.Bigint BIA.
=======
require import AllCore Int Real FSet StdOrder.
require (*--*) BitWord Distr DInterval.
(*---*) import RealOrder RField.
>>>>>>> origin/1.0-preview
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

(* Upper bound on complexity of the adversary *)
type adv_cost = {
  cchoose : int; (* cost *)
  ochoose : int; (* number of call to o *)
  cguess  : int; (* cost *)
  oguess  : int; (* number of call to o *)
}.

op cA : adv_cost.
axiom cA_pos : 0 <= cA.`cchoose /\ 0 <= cA.`ochoose /\ 0 <= cA.`cguess /\ 0 <= cA.`oguess /\ 0 < cA.`ochoose + cA.`oguess.

op qH = cA.`ochoose + cA.`oguess.
lemma gt0_qH :  0 < qH by smt (cA_pos).

(* Assumption: Set CDH *)
clone import DiffieHellman.List_CDH as LCDHT with
  op n <- qH
  proof gt0_n by apply gt0_qH.
import DiffieHellman G FDistr.

clone import LCDHT.C as C1.

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

<<<<<<< HEAD
clone import ROM.Lazy as ROL with
  type from  <- group,
  type to    <- bits,
  op dsample <- fun (x:group), dbits
proof * by exact/dbits_ll.
=======
clone import ROM as RO with
  type in_t    <- group,
  type out_t   <- bits,
  type d_in_t  <- unit,
  type d_out_t <- bool,
  op   dout _  <- dbits.
import Lazy.
clone import ROM_BadCall as ROC with
  op qH <- qH.
>>>>>>> origin/1.0-preview

clone import FMapCost as FMC with
  type from  <- group.

(* Adversary Definitions *)
module type Adversary (O : POracle) = {
  proc choose(pk:pkey): ptxt * ptxt
  proc guess(c:ctxt)  : bool
}.

(* Specializing and merging the hash function *)
<<<<<<< HEAD
module H = {
  var qs : group list
  proc init(): unit = { RO.init(); qs <- []; }
  proc o(x:group): bits = { var y; qs <- x::qs; y <@ RO.o(x); return y; }
  proc hash = RO.o
=======
module H : Hash = {
  proc init(): unit = { LRO.init(); Log.qs <- fset0; }
  proc hash(x:group): bits = { var y; y <@ LRO.o(x); return y; }
>>>>>>> origin/1.0-preview
}.

(* The initial scheme *)
module S = Hashed_ElGamal(H).

(* We want to bound the probability of A winning CPA(Bounder(A,RO),S) in terms of
   the probability of B = CDH_from_CPA(SCDH_from_CPA(A,RO)) winning CDH(B) *)

section.
<<<<<<< HEAD

  declare module A: Adversary [choose : `{N cA.`cchoose, #O.o : cA.`ochoose},
                               guess  : `{N cA.`cguess,  #O.o : cA.`oguess}] {-H}.

  axiom guess_ll (O <: ARO {-A}) : islossless O.o => islossless A(O).guess.
=======
  declare module A: Adversary { LRO, Log, OnBound.G1, OnBound.G_bad }.

  axiom choose_ll (O <: POracle {A}): islossless O.o => islossless A(O).choose.
  axiom guess_ll (O <: POracle {A}) : islossless O.o => islossless A(O).guess.

  local module BA = A(Bound(LRO)).
>>>>>>> origin/1.0-preview

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
<<<<<<< HEAD
      (m0,m1) <@ A(H).choose(gx);
      h       <$ dbits; 
=======
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

  local module (D : ROC.Dist) (H : POracle) = {
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

  local lemma G0_D &m: Pr[G0.main() @ &m: res] = Pr[OnBound.G0(D,LRO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline D(Bound(LRO)).a1 D(Bound(LRO)).a2; wp.
    conseq (_: _ ==> ={b'} /\ b{1} = D.b{2})=> //.
    by inline H.hash; sim.
  qed.

  local lemma G1_D &m: Pr[G1.main() @ &m: res] = Pr[OnBound.G1(D,LRO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline D(Bound(LRO)).a1 D(Bound(LRO)).a2; wp.
    conseq (_: _ ==> ={b'} /\ b{1} = D.b{2})=> //.
    by inline H.hash; sim.
  qed.

  local lemma G2_D &m: Pr[G2.main() @ &m: res] = Pr[OnBound.G_bad(D,LRO).main() @ &m: res].
  proof.
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    inline D(Bound(LRO)).a1 D(Bound(LRO)).a2; wp.
    conseq (_: _ ==> ={glob Log, b'} /\ b{1} = D.b{2} /\ G2.gxy{1} = x{2})=> //.
    by inline H.hash; sim.
  qed.

  local lemma G0_G1_G2 &m:
    Pr[G0.main() @ &m: res] <= Pr[G1.main() @ &m: res] + Pr[G2.main() @ &m: res].
  proof.
  rewrite (G0_D &m) (G1_D &m) (G2_D &m).
  move: (OnBound.ROM_BadCall D _ _ _ &m tt true).
  + move=> H H_o_ll; proc; auto; call (choose_ll H _)=> //; auto=> />.
    by rewrite dt_ll DBool.dbool_ll.
  + by move=> H H_o_ll; proc; auto; call (guess_ll H _)=> //; auto=> />.
  + by move=> _; apply: dbits_ll.
  by rewrite !eqT.
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
>>>>>>> origin/1.0-preview
      c       <- (g ^ y, h);
      b'      <@ A(H).guess(c);
      b       <$ {0,1};
      return (b' = b);
    }
  }.

  local lemma Pr_CPA_G0 &m :
    Pr[CPA(S,A(RO)).main() @ &m: res] <= 
      Pr[G0.main() @ &m: res] + Pr[G0.main() @ &m: G0.gxy \in H.qs].
  proof.
    byequiv => //.
    proc.
<<<<<<< HEAD
    inline Hashed_ElGamal(H).kg Hashed_ElGamal(H).enc H.hash.
    swap{1} 8 -5; swap{2} 10 -3.
    call (_: G0.gxy \in H.qs, 
            (forall x, x \in H.qs{2} = x \in RO.m{2}) /\
            eq_except (pred1 G0.gxy{2}) RO.m{1} RO.m{2}).
    + by apply guess_ll.
    + proc; inline *; auto => /> &1 &2 hb; smt (eq_except_set_eq get_setE).
    + by move=> *; islossless.
    + by move=> /=; proc; call (_: true); 1: islossless; auto => />.
    wp; rnd (fun y0 => y0 +^ m{1}) => /=.
    wp; rnd; call (_: ={RO.m} /\ (forall x, x \in H.qs{2} = x \in RO.m{2})).
    + by proc; inline *; auto => />; smt (get_setE).
    inline *; auto => /> *; split; 1: by move=> *; rewrite mem_empty.
    move=> _ ??? hdom ??; split; 1: by move=> *;ring.
    smt(eq_except_setl get_setE).
=======
    call (_: ={glob LRO, glob Log}); first by sim.
    wp; rnd (fun h, h +^ if b then m1 else m0){1}; rnd.
    call (_: ={glob LRO, glob Log}); first by sim.
    by inline H.init LRO.init; auto=> /> *; split => *; algebra.
>>>>>>> origin/1.0-preview
  qed.

  local lemma Pr_G0_res &m : 
     Pr[G0.main() @ &m: res] <= 1%r/2%r.
  proof.
<<<<<<< HEAD
    byphoare => //; proc.
    rnd (pred1 b'); conseq (_:true) => //.
    by move=> /> *; rewrite DBool.dbool1E.
=======
    have LRO_o_ll := LRO_o_ll _; first by move=> /=; apply: dbits_ll.
    byphoare (_: true ==> res)=> //.
    proc.
    swap 7 3.
    rnd (pred1 b').
    conseq (_: true) => />.
    + by move=> b'; rewrite DBool.dbool1E /pred1 => />.
    islossless.
    + by apply (guess_ll (Bound(LRO))); islossless.
    by apply (choose_ll (Bound(LRO))); islossless.
>>>>>>> origin/1.0-preview
  qed.

  local module ALCDH = {
    proc solve (gx:group, gy:group) : group list = {
      var m0, m1, c, b';
      var h;
      H.init();
      (m0,m1) <@ A(H).choose(gx);
      h       <$ dbits; 
      c       <- (gy, h);
      b'      <@ A(H).guess(c);
      if (H.qs = []) H.qs <- [g];  
      return H.qs;
    }
  }. 

  local lemma cost_ALCDH : 
    choare [ALCDH.solve : true ==> 0 < size res <= cA.`ochoose + cA.`oguess] 
    time [N (6 + cunifin + (3 + cunifin + cget qH + cset qH + cin qH) * (cA.`oguess + cA.`ochoose) + cA.`cguess + cA.`cchoose)].
  proof.
<<<<<<< HEAD
    proc; wp.
    call (_: size H.qs- cA.`ochoose <= k /\ bounded RO.m (size H.qs);
           time
           [(H.o k : [N(3 + cunifin + cget qH + cset qH + cin qH)])]).
    + move=> zo hzo; proc; inline *.
      wp := (bounded RO.m qH).
      by rnd; auto => &hr />; rewrite dbits_ll /=; smt (cset_pos bounded_set).
    wp; rnd; call (_: size H.qs = k /\ bounded RO.m (size H.qs);
           time [(H.o k : [N(3 + cunifin + cget qH + cset qH + cin qH)])]).
    + move=> zo hzo; proc; inline *.
      wp := (bounded RO.m qH).
      rnd;auto => &hr />; rewrite dbits_ll /=; smt(cset_pos bounded_set cA_pos).
    inline *; auto => />.
    split => *.
    + smt (bounded_empty dbits_ll size_ge0 size_eq0 cA_pos).
    rewrite !bigi_constz /=; smt(cA_pos).
  qed.

  local lemma Pr_G0_LCDHPr_G0_res &m: 
    Pr[G0.main() @ &m: G0.gxy \in H.qs] <= Pr[LCDH(ALCDH).main() @ &m : res].
=======
    byequiv (_: ={glob A} ==> ={res})=> //.
    proc.
    call (_: ={glob LRO, glob Log}); first by sim.
    wp; rnd (fun h, h +^ if b then m1 else m0){1}; rnd.
    call (_: ={glob LRO, glob Log}); first by sim.
    by inline H.init LRO.init; auto=> /> *; split => *; algebra.
  qed.

  local equiv G2'_SCDH: G2'.main ~ SCDH(SCDH_from_CPA(A,LRO)).main:
    ={glob A} ==> res{1} = res{2} /\ card Log.qs{1} <= qH.
>>>>>>> origin/1.0-preview
  proof.
    byequiv => //.
    proc.
<<<<<<< HEAD
    conseq (_ : _ ==> G0.gxy{1} \in H.qs{1} => g ^ (x{2} * y{2}) \in s{2}) _ (_: true ==> size s <= qH) => //.
    + by move=> />.
    + call (_: true ==> 0 < size res <= qH); last by auto.
      by conseq cost_ALCDH; smt (cA_pos).
    inline *.
    rnd{1}; auto; call (_: ={glob H}); 1: by sim.
    auto; call (_: ={glob H}); 1: by sim.
    by auto => /> *; rewrite -pow_pow.
  qed.

  lemma ex_reduction &m : 
    exists (B<:CDH.Adversary 
      [solve : `{ N(C1.cduniform_n + 
                  6 + cunifin + 
                  (3 + cunifin + cget qH + cset qH + cin qH) * (cA.`oguess + cA.`ochoose) + cA.`cguess + cA.`cchoose)}]
               {+A, +H}),
    Pr[CPA(S,A(RO)).main() @ &m: res] - 1%r/2%r <= 
    qH%r * Pr[CDH.CDH(B).main() @ &m: res].
=======
    inline SCDH_from_CPA(A,LRO).solve.
    swap{2} 5 -4; swap{1} 7 3.
    rnd{1}; wp.
    seq  8  7: (={glob BA} /\
                c{1} = (gy, h){2} /\
                G2'.gxy{1} = g ^ (x * y){2} /\
                card Log.qs{1} <= qH).
      wp; rnd; call (_: ={glob H} /\ card Log.qs{1} <= qH).
        proc; sp; if=> //; inline Log(LRO).o LRO.o; auto=> />.
        by move=> &2 _ szqs_lt_qH _ _; rewrite fcardU fcard1; smt(fcard_ge0).
      by inline H.init LRO.init; auto=> />; rewrite fcards0; smt(gt0_qH pow_pow).
    call (_: ={glob H} /\ card Log.qs{1} <= qH).
      proc; sp; if=> //; inline Log(LRO).o LRO.o; auto=> /> &2 _ szqs_lt_qH _ _.
      by rewrite fcardU fcard1; smt(fcard_ge0).
    by auto => />.
  qed.

  local lemma Pr_G2'_SCDH &m :
    Pr[G2'.main() @ &m: res]
    = Pr[SCDH(SCDH_from_CPA(A,LRO)).main() @ &m : res]
  by byequiv G2'_SCDH.

  local lemma Reduction &m :
    Pr[CPA(S,BA).main() @ &m : res] <=
    1%r / 2%r + Pr[SCDH(SCDH_from_CPA(A,LRO)).main() @ &m : res].
>>>>>>> origin/1.0-preview
  proof.
    have [B hB]:= C1.ex_reduction _ ALCDH &m cost_ALCDH.
    exists B; split.
    + proc true : time [] => // /#.
    move: (Pr_CPA_G0 &m) (Pr_G0_res &m) (Pr_G0_LCDHPr_G0_res) => /#.
  qed.

<<<<<<< HEAD
=======
  (** Composing reduction from CPA to SCDH with reduction from SCDH to CDH *)
  lemma Security &m:
      Pr[CPA(S,A(Bound(LRO))).main() @ &m: res] - 1%r / 2%r <=
      qH%r * Pr[CDH.CDH(CDH_from_SCDH(SCDH_from_CPA(A,LRO))).main() @ &m: res].
  proof.
    apply (ler_trans (Pr[SCDH(SCDH_from_CPA(A,LRO)).main() @ &m: res])).
    + smt(Reduction).
    have:= Self.SCDH.Reduction (SCDH_from_CPA(A,LRO)) &m gt0_qH.    
    by rewrite -mulrA mul1r mulrC ler_pdivr_mulr 1:lt_fromint 1:gt0_qH mulrC.
  qed.
>>>>>>> origin/1.0-preview
end section.

print ex_reduction.
