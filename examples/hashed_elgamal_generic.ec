require import AllCore FSet List SmtMap.
require (*--*) BitWord Distr DInterval.
(*---*) import StdOrder.RealOrder StdRing.RField StdBigop.Bigint BIA.
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

clone import ROM.Lazy as ROL with
  type from  <- group,
  type to    <- bits,
  op dsample <- fun (x:group), dbits
proof * by exact/dbits_ll.

(* Adversary Definitions *)
module type Adversary (O:ARO) = {
  proc choose(pk:pkey): ptxt * ptxt
  proc guess(c:ctxt)  : bool
}.

(* Specializing and merging the hash function *)
module H = {
  var qs : group list
  proc init(): unit = { RO.init(); qs <- []; }
  proc o(x:group): bits = { var y; qs <- x::qs; y <@ RO.o(x); return y; }
  proc hash = RO.o
}.

(* The initial scheme *)
module S = Hashed_ElGamal(H).

(*
(* The reduction *)
module SCDH_from_CPA(A:Adversary,O:Oracle): SCDHT.Adversary = {
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
*)
(* We want to bound the probability of A winning CPA(Bounder(A,RO),S) in terms of
   the probability of B = CDH_from_CPA(SCDH_from_CPA(A,RO)) winning CDH(B) *)

(* FIXME: move this *)
schema cost_eqnil ['a] `{P} {l:'a list} : cost [P: l = []] = cost [P:l] + 1.
hint simplify cost_eqnil.

schema cost_oget ['a] `{P} {o: 'a option} : 
  cost [P : oget o] = cost [P:o] + 1.
hint simplify cost_oget.

schema cost_empty ['a 'b] `{P} :
  cost [P: empty<:'a, 'b>] = 1.
hint simplify cost_empty.

op bounded ['from 'to] (m : ('from, 'to)fmap) (size:int) = 
   card (fdom m) <= size.

lemma bounded_set ['from 'to] (m : ('from, 'to)fmap) (size:int) x e : 
  bounded m size => bounded (m.[x<-e]) (size + 1).
proof. by rewrite /bounded fdom_set fcardU fcard1; smt (fcard_ge0). qed.

lemma bounded_empty ['from 'to] : bounded empty<:'from, 'to> 0.
proof. by rewrite /bounded fdom0 fcards0. qed.

abstract theory FMapCost.
  type from.
  type to.

  op cget : int -> int.
  op cset : int -> int.
  op cin  : int -> int.

  axiom cget_pos (x:int) : 0 <= cget x.
  axiom cset_pos (x:int) : 0 <= cset x.
  axiom cin_pos (x:int) : 0 <= cin x.

 
  (* Fixme, this need to be generalized in the schema *)
  (* maximal size of the map *)
  op max_size : int.

  schema cost_get_P ['a 'b] `{P} {m:('a, 'b) fmap, x:'a} :
    cost [P /\ bounded m max_size : m.[x]] = cost[P:m] + cost[P:x] + cget max_size.

  schema cost_set_P ['a 'b] `{P} {m:('a, 'b) fmap, x:'a, e:'b} :
    cost [P /\ bounded m max_size : m.[x<-e]] = cost[P:m] + cost[P:x] + cost[P:e] + cset max_size.

  schema cost_in_P ['a 'b] `{P} {m:('a, 'b) fmap, x:'a} :
    cost [P /\ bounded m max_size: x \in m] = cost[P:m] + cost[P:x] + cin max_size.

  hint simplify cost_get_P, cost_set_P, cost_in_P.

  schema cost_get ['a 'b] {m:('a, 'b) fmap, x:'a} :
    cost [bounded m max_size : m.[x]] = cost[true:m] + cost[true:x] + cget max_size.

  schema cost_set ['a 'b] {m:('a, 'b) fmap, x:'a, e:'b} :
    cost [bounded m max_size : m.[x<-e]] = cost[true:m] + cost[true:x] + cost[true:e] + cset max_size.

  schema cost_in ['a 'b] {m:('a, 'b) fmap, x:'a} :
    cost [bounded m max_size: x \in m] = cost[true:m] + cost[true:x] + cin max_size.

  hint simplify cost_get, cost_set, cost_in.

end FMapCost.

clone import FMapCost as FMC with
  type from  <- group,
  type to    <- bits,
  op max_size <- qH.

section.

  declare module A: Adversary [choose : `{cA.`cchoose, #O.o : cA.`ochoose},
                               guess  : `{cA.`cguess,  #O.o : cA.`oguess}] {-H}.

  axiom guess_ll (O <: ARO {-A}) : islossless O.o => islossless A(O).guess.

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
    Pr[CPA(S,A(RO)).main() @ &m: res] <= 
      Pr[G0.main() @ &m: res] + Pr[G0.main() @ &m: G0.gxy \in H.qs].
  proof.
    byequiv => //.
    proc.
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

  op foo : int.

  local lemma cost_ALCDH : 
    choare [ALCDH.solve : true ==> 0 < size res <= cA.`ochoose + cA.`oguess] 
    time [6 + cunifin + (3 + cunifin + cget qH + cset qH + cin qH) * (cA.`oguess + cA.`ochoose) + cA.`cguess + cA.`cchoose].
  proof.
    proc; wp.
    call (_: bounded RO.m (size H.qs);
           (H.o : size H.qs- cA.`ochoose)
           time
           [(H.o : [fun _ => 3 + cunifin + cget qH + cset qH + cin qH])]).
    + move=> zo hzo; proc; inline *.
      wp : (bounded RO.m qH).
      by auto => &hr />; rewrite dbits_ll /=; smt (cset_pos bounded_set).
    auto; call (_: bounded RO.m (size H.qs);
           (H.o : size H.qs)
           time [(H.o : [fun _ => 3 + cunifin + cget qH + cset qH + cin qH])]).
    + move=> zo hzo; proc; inline *.
      wp : (bounded RO.m qH).
      auto => &hr />; rewrite dbits_ll /=; smt(cset_pos bounded_set cA_pos).
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
    by auto => /> *; rewrite -pow_pow.
  qed.

  lemma ex_reduction &m : 
    exists (B<:CDH.Adversary 
      [solve : `{ C1.cduniform_n + 
                  6 + cunifin + 
                  (3 + cunifin + cget qH + cset qH + cin qH) * (cA.`oguess + cA.`ochoose) + cA.`cguess + cA.`cchoose}]
               {+A, +H}),
    Pr[CPA(S,A(RO)).main() @ &m: res] - 1%r/2%r <= 
    qH%r * Pr[CDH.CDH(B).main() @ &m: res].
  proof.
    have [B hB]:= C1.ex_reduction _ ALCDH &m cost_ALCDH.
    exists B; split.
    + proc true : time [] => // /#.
    move: (Pr_CPA_G0 &m) (Pr_G0_res &m) (Pr_G0_LCDHPr_G0_res) => /#.
  qed.

end section.

print ex_reduction.


