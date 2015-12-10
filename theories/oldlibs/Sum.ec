(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import List FSet Int Real OldMonoid.

(* temporary workaround *)
op intval : int -> int -> int fset = fun (i j:int) =>
  oflist (List.Iota.iota_ i (j - i + 1)).

lemma intval_def i i1 i2:
  mem (intval i1 i2) i <=> (i1<= i /\ i <= i2)
by [].

lemma intval_card_0 i1 (i2 : int):
  i1 <= i2 =>
  card (intval i1 i2) = i2 - i1 + 1.
proof.
  move=> le_i1_i2; rewrite cardE.
  rewrite -(perm_eq_size (iota_ i1 (i2 - i1 + 1))) 2:size_iota 2:smt.
  by rewrite -(undup_id (iota_ i1 (i2 - i1 + 1))) 1:iota_uniq// /intval oflistK// iota_uniq//.
qed.

lemma intval_card_1 (i1 i2:int):
  i2 < i1 => card (intval i1 i2) = 0
by [].

op int_sum: (int -> real) -> int fset -> real = Mrplus.sum.

pred is_cnst (f : int -> 'a) = forall i1 i2, f i1 = f i2.

lemma int_sum_const (f : int -> real) (s: int fset):
  is_cnst f => int_sum f s = (card s)%r * f 0.
proof strict.
by move=> is_cnst;
   rewrite /int_sum (Mrplus.NatMul.sum_const (f 0)) // => x hh;
   apply is_cnst.
qed.


