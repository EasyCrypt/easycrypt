(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Int Real Distr List FSet.

pragma +implicits.

(* -------------------------------------------------------------------- *)
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
  X <> fset0 <=> mu (dU X) predT = 1%r.
proof.
  rewrite mu_dU.
  have ->: filter predT X = X
    by rewrite filterE filter_predT elemsK.
  by case (X = fset0)=> //=; smt full.
qed.

lemma support_dU (X : 'a fset) x:
  X <> fset0 =>
  support (dU X) x <=> mem X x.
proof.
  (* Dealing with the stupid notation mismatches *)
  rewrite /support /in_supp /mu_x.
  (* Actually doing the proof *)
  by rewrite mux_dU /int_of_bool; case (mem X x); smt.
qed.
