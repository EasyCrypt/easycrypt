(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(** Uniform distributions over a list of elements with multiplicity. **)
(* This should be replaced with a NewDistr when we switch. *)
require import Fun Pred Int Real List Distr.
require NewDistr.

op dmulti (s : 'a list): 'a distr.

axiom dmultiE (s : 'a list) (E : 'a -> bool):
  mu (dmulti s) E = (count (predI (mem s) E) s)%r / (size s)%r.

(* When switching to NewDistr, this becomes the definition, the above
   becomes a lemma. *)
lemma dmulti1E (s : 'a list) (x : 'a):
  mu (dmulti s) (pred1 x)
  = if mem s x then (count (pred1 x) s)%r / (size s)%r else 0%r.
proof.
rewrite dmultiE; case: (mem s x)=> //= [x_in_s|x_notin_s].
  do 3!congr. apply/fun_ext=> x'; rewrite eq_iff.
  by case (x' = x)=> //=; rewrite /predI /pred1 /= => ->.
have ->: predI (mem s) (pred1 x) = pred0.
  apply/fun_ext=> x'; rewrite /predI /pred1 eq_iff.
  by case (x' = x)=> [->|].
rewrite count_pred0; case ((size s)%r = 0%r)=> [->|h].
  by rewrite StdRing.divr0.
by rewrite div_def// StdRing.RField.mul0r.
qed.

lemma eq_dmultiP (s1 s2 : 'a list):
  perm_eq s1 s2 =>
  dmulti s1 = dmulti s2.
proof.
move=> h; have:= h; have:= h.
move: h=> /perm_eq_mem mem_eq /perm_eq_size size_eq /perm_eqP count_eq.
by apply/pw_eq=> x; rewrite /mu_x !dmulti1E mem_eq size_eq count_eq.
qed.
