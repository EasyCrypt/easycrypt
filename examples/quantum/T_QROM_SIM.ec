require import AllCore List Distr DBool DProd DList DInterval CHoareTactic IntDiv.
(*   *) import StdOrder RField RealOrder StdBigop Bigreal BRA.
require (*  *) Matrix Tuple (* FinType *).
require (****) T_QROM.

abstract theory T_QROM_SIM.

op q : int.

axiom q_ge0 : 0 <= q.

(* Sampling is based on two finite fields with the same characteristic. *)
op p : { int | 1 < p } as gt1_p.

type ff.
op enum_ff : ff list.
op n : { int | 0 < n } as gt0_n.
axiom ff_order : size enum_ff = p^n.

clone  MFinite as FF with
  type t <- ff,
  op Support.enum <- enum_ff.

lemma in_char_order : p %| FF.Support.card. 
have -> : (p = p^1); first by smt(@Ring.IntID).
by rewrite /card  ff_order; apply dvdz_exp2l; smt(gt0_n).
qed.

clone import T_QROM with
   type from = ff,
   type hash = ff.

clone import Matrix with
  type R <- ff,
  op size <- 2*q
  proof ge0_size by smt(q_ge0).

op genseed = dvector FF.dunifin.

(* We use exponentiation to generate a row in a Vandermonde matrix *)
op (^) : ff -> int -> ff.

op compute(seed : vector, x : from) : hash =
        let xv = offunv (fun (i : int) => x^i) in
             dotp xv seed.
            
module LQRO : QRO_i = {
  var seed : vector

  proc init() = { seed <$ genseed; }

  quantum proc h {x:from} = { return compute seed x; }

}.


op dcompute : (from -> hash) distr = 
       dmap genseed (fun seed => compute seed).

clone import QROM_Fundamental_Lemma with
    op q <- q
    proof q_ge0 by smt(q_ge0).

lemma eager_sampling  (A<:AdvRO{-QRO, -LQRO}[main : `{Inf, #H.h : q}]) &m (r : result):
  Pr[ QRO_main(A,LQRO).main() @ &m: res = r] = Pr[ QRO_main_D(A).main(dcompute) @ &m: res = r]. 
byequiv. 
proc. inline *.
(* This is moving the compute function from the oracle on the left
   to the sampled function on the right. *)
admitted.

import TupleXY.

lemma perfect_sim xy:
  xy \in wordn (2 * q) =>
 mu dfhash (fun (fx : from -> hash) => all (fun (xr : from * hash) => fx xr.`1 = xr.`2) xy) =
 mu dcompute (fun (fx : from -> hash) => all (fun (xr : from * hash) => fx xr.`1 = xr.`2) xy).
proof.
move => xys.
pose P := (fun (fx : from -> hash) => all (fun (xr : from * hash) => fx xr.`1 = xr.`2) xy).
rewrite /dfhash /dcompute /compute.
(* This is the lemma PY proved *)
admitted.

lemma efficient_sim (A<:AdvRO{-QRO, -LQRO}[main : `{Inf, #H.h : q}]) &m (r : result):
  Pr[ QRO_main(A,QRO).main() @ &m: res = r ] = Pr[ QRO_main(A,LQRO).main() @ &m: res = r ].
proof.
have -> : 
 Pr[ QRO_main(A,QRO).main() @ &m: res = r ] = Pr[QRO_main_D(A).main(dfhash) @ &m : res = r].
   by byequiv=>//; conseq (_: _ ==> ={res})=> //; proc;inline*; sim; auto => />.
move : (dA_split A &m) => dA_split.
elim dA_split => C dA_split.
rewrite (eager_sampling A) (dA_split dfhash r) (dA_split dcompute r).
by apply (eq_big_seq _ _  (wordn (2*q))); move => * /=;congr; apply perfect_sim.
qed.

end T_QROM_SIM.

