(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List FSet Finite Real Distr OldMonoid.
require DBool.

require Means.

theory MeansBool.

  clone export Means as M with
  type input <- bool,
  op d <- {0,1}.

  lemma Mean (A<:Worker) &m (p: bool -> glob A -> output -> bool):
     Pr[Rand(A).main() @ &m : p (fst res) (glob A) (snd res)] =
     1%r/2%r*(Pr[A.work(true) @ &m : p true (glob A) res] +
                Pr[A.work(false) @ &m : p false (glob A) res]).
  proof.
    cut Hf : is_finite (support {0,1})
      by exists ([true;false]) => x; smt.
    cut := Mean A &m p => /= -> //.
    cut -> : oflist (to_seq (support {0,1}))
             = (fset0 `|` fset1 true `|` fset1 false).
      by apply/fsetP=> x; rewrite !inE mem_oflist mem_to_seq//; smt.
    rewrite Mrplus.sum_add /=;first smt.
    rewrite Mrplus.sum_add /=;first smt.
    rewrite Mrplus.sum_empty /= !DBool.dbool1E.
    cut Hd: 2%r <> 0%r by smt.
    by algebra.
  qed.

end MeansBool.

clone import MeansBool as MB with
  type M.output <- bool.

lemma Sample_bool (A<:Worker) &m (p:glob A -> bool):
  Pr[Rand(A).main() @ &m : fst res = snd res /\ p (glob A)] -
  Pr[A.work(false) @ &m : p (glob A)]/2%r =
      1%r/2%r*(Pr[A.work(true) @ &m : res /\ p (glob A)] -
               Pr[A.work(false) @ &m : res /\ p (glob A)]).
proof strict.
  cut := Mean A &m (fun b (gA:glob A) (b':bool), b = b' /\ p gA) => /= ->.
  cut Hd: 2%r <> 0%r by smt.
  cut -> : Pr[A.work(true) @ &m : true = res /\ p (glob A)] =
           Pr[A.work(true) @ &m : res /\ p (glob A)].
    by rewrite Pr[mu_eq];smt.
  cut -> : Pr[A.work(false) @ &m : false = res /\ p (glob A)] =
           Pr[A.work(false) @ &m : !res /\ p (glob A)].
    by rewrite Pr[mu_eq];smt.
  cut -> : Pr[A.work(false) @ &m : p (glob A)] =
           Pr[A.work(false) @ &m : (!res /\ p (glob A)) \/ (res /\ p (glob A))].
    by rewrite Pr[mu_eq];smt.
  rewrite Pr[mu_disjoint];first smt.
  by field.
qed.

lemma Sample_bool_lossless (A<:Worker) &m:
  Pr[A.work(false) @ &m : true] = 1%r =>
  Pr[Rand(A).main() @ &m : fst res = snd res] - 1%r/2%r =
      1%r/2%r*(Pr[A.work(true) @ &m : res] - Pr[A.work(false) @ &m : res]).
proof strict.
  move=> Hloss.
  cut := Sample_bool A &m (fun x, true) => /= <-.
  by rewrite Hloss.
qed.
