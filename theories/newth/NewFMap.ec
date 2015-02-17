(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

require import Pred.
require import Option.
require import Pair.
require import Int.
require import NewList.
require import NewFSet.
search has.

(* TODO: this may be of more general interest and may benefit from a
         move to NewList, or a separate PairList theory. *)
op fst (xs : ('a * 'b) list) =
  with xs = "[]"      => []
  with xs = (::) x xs => x.`1::fst xs.

op undup_fst (xs : ('a * 'b) list) =
  with xs = "[]"      => []
  with xs = (::) x xs => if mem (fst xs) x.`1
                         then undup_fst xs
                         else x::undup_fst xs.

op uniq_fst (xs : ('a * 'b) list) =
  with xs = "[]"      => true
  with xs = (::) x xs => !mem (fst xs) x.`1 /\ uniq_fst xs.

lemma mem_fst_mem (xs : ('a * 'b) list) (ab : 'a * 'b):
  mem xs ab => mem (fst xs) ab.`1.
proof.
  by elim xs=> //= x xs IH [-> //= | /IH ->].
qed.

lemma uniq_fst_uniq (xs : ('a * 'b) list):
  uniq_fst xs =>
  uniq (fst xs).
proof.
  by elim xs=> //= x xs IH [] ->.
qed.

lemma mem_fst_undup_fst (xs : ('a * 'b) list):
  mem (fst (undup_fst xs)) <= mem (fst xs).
proof.
  elim xs=> //= x xs IH.
  case (mem (fst xs) x.`1).
    by move=> x1_in_fstxs a /IH; rewrite in_cons=> ->.
    by move=> x1_notin_fstxs a; rewrite !in_cons=> [-> | /IH ->].
qed.

lemma uniq_undup_fst (xs : ('a * 'b) list): uniq_fst (undup_fst xs).
proof.
  elim xs=> //= x xs IH.
  case (mem (fst xs) x.`1)=> //=.
  rewrite IH /= => x1_notin_fstundup; rewrite -not_def.
  by move=> /mem_fst_undup_fst.
qed.

(* -------------------------------------------------------------------- *)
(* Finite maps are abstractely represented as the quotient by
 * [perm_eq] of lists of pairs without first projection duplicates. *)

type ('a,'b) fmap.

op elems  : ('a,'b) fmap -> ('a * 'b) list.
op oflist : ('a * 'b) list -> ('a,'b) fmap.

axiom elemsK  (m : ('a,'b) fmap): Self.oflist (elems  m) = m.
axiom oflistK (s : ('a * 'b) list): perm_eq (undup_fst s) (elems (Self.oflist s)).

lemma uniq_keys (m : ('a,'b) fmap): uniq_fst (elems m).
proof.
  rewrite -(elemsK m); move: (elems m) => {m} m.
  admit. (* TODO: fill in this proof *)
qed.

axiom fmap_eq (s1 s2 : ('a,'b) fmap):
  (perm_eq (elems s1) (elems s2)) => (s1 = s2).
