(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Real Distr NewList NewFSet.

pragma +implicits.

(* -------------------------------------------------------------------- *)
theory U.
  op dU: 'a fset -> 'a distr.

  (* TODO: This is dangerous: if 0/0 is defined as 1, we die *)
  axiom mu_dU (X : 'a fset) e:
      mu (dU X) e
    = (card (filter e X))%r/(card X)%r.

  lemma mux_dU (X : 'a fset) x:
    mu (dU X) (pred1 x) = (int_of_bool (mem X x))%r/(card X)%r.
  proof.
    (* TODO: Reinforce the filter and card abstractions to avoid
       having to poke holes in it *)
    rewrite mu_dU {1}cardE filterE.
    have <- := perm_eq_size _ _ (oflistK (filter (pred1 x) (elems X))).
    rewrite undup_id 1:filter_uniq 1:uniq_elems //.
    by rewrite size_filter count_uniq_mem 1:uniq_elems// -memE.
  qed.

  lemma dU_ll (X : 'a fset):
    X <> set0 <=> mu (dU X) predT = 1%r.
  proof.
    rewrite mu_dU.
    have ->: filter predT X = X
      by rewrite filterE filter_predT elemsK.
    by case (X = set0)=> //=; smt full.
  qed.

  lemma support_dU (X : 'a fset) x:
    X <> set0 =>
    support (dU X) x <=> mem X x.
  proof.
    (** Dealing with the stupid notation mismatches **)
    rewrite /support /in_supp /mu_x.
    rewrite (_: ((=) x) = pred1 x) 1:-ExtEq.fun_ext; 1:by move=> y; rewrite @(eq_sym x).
    (* Actually doing the proof *)
    rewrite U.mux_dU.
    by case (mem X x); rewrite /int_of_bool //=; smt full.
  qed.
end U.
