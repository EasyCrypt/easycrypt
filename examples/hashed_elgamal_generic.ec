require import AllCore FSet List SmtMap CHoareTactic StdOrder.
require (*--*) BitWord Distr DInterval.
(*---*) import RealOrder RField StdBigop.Bigint BIA.
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

op cdbits : { int | 0 <= cdbits } as ge0_cdbits.

schema cost_cdbits `{P} : cost [P: dbits] = N cdbits.
hint simplify cost_cdbits.

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
clone DiffieHellman as DH.

clone import DH.List_CDH as LCDHT with
  op n <- qH
  proof gt0_n by apply gt0_qH.
import DH.DDH DH.G DH.GP DH.FD DH.GP.ZModE.

clone import LCDHT.Cost as C1.

clone include AllCore.Cost.
clone include Bool.Cost.
clone include Bits.Cost.
clone include DBool.Cost.
clone include List.Cost.
clone include DH.GP.Cost.

type pkey = group.
type skey = exp.
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

clone import ROM as RO with
  type in_t    <- group,
  type out_t   <- bits,
  type d_in_t  <- unit,
  type d_out_t <- bool,
  op   dout _  <- dbits.

import Lazy.

clone import ROM_BadCall as ROC with
  op qH <- qH.

clone import FMapCost as FMC with
  type from  <- group.

(* Adversary Definitions *)
module type Adversary (O : POracle) = {
  proc choose(pk:pkey): ptxt * ptxt
  proc guess(c:ctxt)  : bool
}.

(* Specializing and merging the hash function *)

module H = {
  var qs : group list
  proc init(): unit = { LRO.init(); qs <- []; }
  proc o(x:group): bits = { var y; qs <- x::qs; y <@ LRO.o(x); return y; }
  proc hash = LRO.o
}.

(* The initial scheme *)
module S = Hashed_ElGamal(H).

(* We want to bound the probability of A winning CPA(Bounder(A,RO),S) in terms of
   the probability of B = CDH_from_CPA(SCDH_from_CPA(A,RO)) winning CDH(B) *)

section.
  declare module A <: Adversary [choose : `{N cA.`cchoose, #O.o : cA.`ochoose},
                                 guess  : `{N cA.`cguess,  #O.o : cA.`oguess}] {-H}.

  declare axiom guess_ll (O <: POracle {-A}) : islossless O.o => islossless A(O).guess.

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
      (m0,m1) <@ A(H).choose(gx);
      h       <$ dbits;
      c       <- (g ^ y, h);
      b'      <@ A(H).guess(c);
      b       <$ {0,1};
      return (b' = b);
    }
  }.

  local lemma Pr_CPA_G0 &m :
    Pr[CPA(S,A(LRO)).main() @ &m: res] <=
      Pr[G0.main() @ &m: res] + Pr[G0.main() @ &m: G0.gxy \in H.qs].
  proof.
    byequiv => //.
    proc.
    inline Hashed_ElGamal(H).kg Hashed_ElGamal(H).enc H.hash.
    swap{1} 8 -5; swap{2} 10 -3.
    call (_: G0.gxy \in H.qs,
            (forall x, x \in H.qs{2} = x \in LRO.m{2}) /\
            eq_except (pred1 G0.gxy{2}) LRO.m{1} LRO.m{2}).
    + by apply guess_ll.
    + proc; inline *; auto => /> &1 &2 hb; smt (eq_except_set_eq get_setE).
    + by move=> *; islossless.
    + by move=> /=; proc; call (_: true); 1: islossless; auto => />.
    wp; rnd (fun y0 => y0 +^ m{1}) => /=.
    wp; rnd; call (_: ={LRO.m} /\ (forall x, x \in H.qs{2} = x \in LRO.m{2})).
    + by proc; inline *; auto => />; smt (get_setE).
    inline *; auto => /> *; split; 1: by move=> *; rewrite mem_empty.
    move=> _ ??? hdom ??; split; 1: by move=> *;ring.
    smt(eq_except_setl get_setE).
  qed.

  local lemma Pr_G0_res &m :
     Pr[G0.main() @ &m: res] <= 1%r/2%r.
  proof.
    byphoare => //; proc.
    rnd (pred1 b'); conseq (_:true) => //.
    by move=> /> *; rewrite DBool.dbool1E.
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
    time [N (6 + cdbits + (3 + cdbits + cget qH + cset qH + cin qH) * (cA.`oguess + cA.`ochoose) + cA.`cguess + cA.`cchoose)].
  proof.
    proc; wp.
    call (_: size H.qs- cA.`ochoose <= k /\ bounded LRO.m (size H.qs);
           time
           [H.o k : [N(3 + cdbits + cget qH + cset qH + cin qH)]]).
    + move=> zo hzo; proc; inline *.
      wp := (bounded LRO.m qH).
      rnd; auto => &hr />; rewrite dbits_ll /=.
      progress; 1,2,4,6,7,8,9: smt (cset_pos bounded_set).
      * have -> : (qH = qH - 1 + 1) by smt ().
        apply bounded_set.
        smt ().

      * rewrite addzC.
        apply bounded_set.
        smt ().

    wp; rnd; call (_: size H.qs = k /\ bounded LRO.m (size H.qs);
           time [H.o k : [N(3 + cdbits + cget qH + cset qH + cin qH)]]).
    + move=> zo hzo; proc; inline *.
      wp := (bounded LRO.m qH).
      rnd;auto => &hr />; rewrite dbits_ll /=.
      progress; 1,2,4,6,7,8,9:
      smt(cset_pos bounded_set cA_pos).
      * have -> : (qH = qH - 1 + 1) by smt ().
        apply bounded_set.
        smt (cA_pos).

      * rewrite addzC.
        apply bounded_set.
        smt ().
    inline *; auto => />.
    split => *.
    + smt (bounded_empty dbits_ll size_ge0 size_eq0 cA_pos).
    rewrite !bigi_constz /=; smt(cA_pos).
  qed.

  local lemma Pr_G0_LCDHPr_G0_res &m:
    Pr[G0.main() @ &m: G0.gxy \in H.qs] <= Pr[LCDH(ALCDH).main() @ &m : res].
  proof.
    byequiv => //.
    proc.
    conseq (_ : _ ==> G0.gxy{1} \in H.qs{1} => g ^ (x{2} * y{2}) \in s{2}) _ (_: true ==> size s <= qH) => //.
    + by move=> />.
    + call (_: true ==> 0 < size res <= qH); last by auto.
      by conseq cost_ALCDH; smt (cA_pos).
    inline *.
    rnd{1}; auto; call (_: ={glob H}); 1: by sim.
    auto; call (_: ={glob H}); 1: by sim.
    by auto => /> *; rewrite expM.
  qed.

  lemma ex_reduction &m :
    exists (B<:DH.CDH.Adversary
      [solve : `{ N(C1.cduniform_n +
                  6 + cdbits +
                  (3 + cdbits + cget qH + cset qH + cin qH) * (cA.`oguess + cA.`ochoose) + cA.`cguess + cA.`cchoose)}]
               {+A, +H}),
    Pr[CPA(S,A(LRO)).main() @ &m: res] - 1%r/2%r <=
    qH%r * Pr[DH.CDH.CDH(B).main() @ &m: res].
  proof.
    have [B hB]:= C1.ex_reduction _ ALCDH &m cost_ALCDH.
    exists B; split.
    + proc true : time [] => // /#.
    move: (Pr_CPA_G0 &m) (Pr_G0_res &m) (Pr_G0_LCDHPr_G0_res) => /#.
  qed.

end section.

print ex_reduction.
