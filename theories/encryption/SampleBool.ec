(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List Finite Real Distr.
require DBool.

require Means.

theory MeansBool.
clone export Means as M with
  type input <- bool,
    op d <- {0,1}.
import StdBigop.Bigbool.BBOr StdBigop.Bigreal.BRA.

lemma Mean (A<:Worker) &m (p: bool -> glob A -> output -> bool):
   Pr[Rand(A).main() @ &m : p (fst res) (glob A) (snd res)] =
   1%r/2%r*(Pr[A.work(true) @ &m : p true (glob A) res] +
              Pr[A.work(false) @ &m : p false (glob A) res]).
proof.
have Hf : is_finite (support {0,1}).
+ by exists ([true;false])=> - []; rewrite DBool.supp_dbool.
have:= Mean_uni A &m p (1%r/2%r) => /= -> //.
+ by move=> x _; rewrite DBool.dbool1E.
rewrite (eq_big_perm _ _ _ [true; false]).
+ apply: uniq_perm_eq=> //=.
  + exact: uniq_to_seq.
  by move=> x; rewrite mem_to_seq // DBool.supp_dbool; case: x.
by rewrite big_cons big_cons big_nil.
qed.
end MeansBool.

clone import MeansBool as MB with
  type M.output <- bool.

lemma Sample_bool (A <: Worker) &m (p:glob A -> bool):
  Pr[Rand(A).main() @ &m : fst res = snd res /\ p (glob A)] -
  Pr[A.work(false) @ &m : p (glob A)]/2%r =
      1%r/2%r*(Pr[A.work(true) @ &m : res /\ p (glob A)] -
               Pr[A.work(false) @ &m : res /\ p (glob A)]).
proof.
have:= Mean A &m (fun b (gA:glob A) (b':bool), b = b' /\ p gA)=> //= ->.
have Hd: 2%r <> 0%r by smt().
have -> : Pr[A.work(true) @ &m : true = res /\ p (glob A)] =
          Pr[A.work(true) @ &m : res /\ p (glob A)].
+ by rewrite Pr[mu_eq] /#.
have -> : Pr[A.work(false) @ &m : false = res /\ p (glob A)] =
          Pr[A.work(false) @ &m : !res /\ p (glob A)].
+ by rewrite Pr[mu_eq] /#.
have -> : Pr[A.work(false) @ &m : p (glob A)] =
          Pr[A.work(false) @ &m : (!res /\ p (glob A)) \/ (res /\ p (glob A))].
+ by rewrite Pr[mu_eq] /#.
rewrite Pr[mu_disjoint] 1:/#.
by algebra.
qed.

lemma Sample_bool_lossless (A <: Worker) &m:
  Pr[A.work(false) @ &m : true] = 1%r =>
  Pr[Rand(A).main() @ &m : fst res = snd res] - 1%r/2%r =
      1%r/2%r*(Pr[A.work(true) @ &m : res] - Pr[A.work(false) @ &m : res]).
proof.
move=> Hloss.
have := Sample_bool A &m (fun x, true) => /= <-.
by rewrite Hloss.
qed.
