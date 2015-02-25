(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

require import Option Int NewList.
pragma +implicits.

(* -------------------------------------------------------------------- *)
type 'a array = 'a list.

op "_.[_]": 'a array -> int -> 'a = nth witness
  axiomatized by getE.

lemma arrayP (a1 a2 : 'a array):
  (a1 = a2) <=> size a1 = size a2 /\ (forall i, 0 <= i < size a2 => a1.[i] = a2.[i]).
proof.
  split=> [-> //= | []].
  elim a2 a1=> /=.
    by move=> a1; rewrite size_eq0=> ->.
  move=> x xs ih [//= | //= x' xs' /addzI eq_sizes h].
    by rewrite eq_sym addzC addz1_neq0 1:size_ge0.
  split.
    by have //= := h 0 _; rewrite ?getE //= -lez_add1r lez_addl size_ge0.
  apply ih=> //.
  move=> i [le0_i lti_lenxs]; have:= h (i + 1) _.
    smt. (* side conditions... *)
  by rewrite getE /= addz1_neq0 //= addAzN.
qed.

op "_.[_<-_]" (xs : 'a array) (n : int) (x : 'a) =
  take (size xs) ((take n xs) ++ [x] ++ (drop (n + 1) xs))
  axiomatized by setE.

lemma size_set (xs : 'a array) (n : int) (a : 'a):
  size xs.[n<-a] = size xs.
proof.
  rewrite setE size_take 1:size_ge0 // !size_cat /=.
  smt. (* This is a case analysis... smt's strong suit. *)
qed.
  