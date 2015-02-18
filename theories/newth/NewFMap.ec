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

(* TODO: this may be of more general interest and may benefit from a
         move to NewList, or a separate PairList theory. *)
op fst (xs : ('a * 'b) list) =
  with xs = "[]"      => []
  with xs = (::) x xs => x.`1::fst xs.

op snd (xs : ('a * 'b) list) =
  with xs = "[]"      => []
  with xs = (::) x xs => x.`2::snd xs.

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

lemma mem_snd_mem (xs : ('a * 'b) list) (ab : 'a * 'b):
  mem xs ab => mem (snd xs) ab.`2.
proof.
  by elim xs=> //= x xs IH [-> //= | /IH ->].
qed.

lemma mem_fst_ex_snd (xs : ('a * 'b) list) (x : 'a):
  mem (fst xs) x <=> (exists y, mem xs (x,y)).
proof.
  split; last by move=> [] y /mem_fst_mem.
  elim xs=> //= [[a b]] xs IH /= [].
    by move=> -> /=; exists b.
  by move=> /IH [] y xy_in_xs; exists y; right.
qed.

lemma mem_snd_ex_fst (xs : ('a * 'b) list) (y : 'b):
  mem (snd xs) y <=> (exists x, mem xs (x,y)).
proof.
  split; last by move=> [] x /mem_snd_mem.
  elim xs=> //= [[a b]] xs IH /= [].
    by move=> -> /=; exists a.
  by move=> /IH [] x xy_in_xs; exists x; right.
qed.

lemma uniq_fst_uniq_fst (xs : ('a * 'b) list):
  uniq_fst xs =>
  uniq (fst xs).
proof.
  by elim xs=> //= x xs IH [] ->.
qed.

lemma uniq_fst_uniq (xs : ('a * 'b) list):
  uniq_fst xs =>
  uniq xs.
proof.
  elim xs=> //= x xs IH [] x1_notin_fstxs /IH uniq_xs.
  by split=> //; rewrite -not_def=> /mem_fst_mem.
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

lemma uniq_perm_eq_fst (s1 s2 : ('a * 'b) list):
  uniq_fst s1 =>
  uniq_fst s2 =>
  (forall (x : 'a * 'b), mem s1 x <=> mem s2 x) =>
  perm_eq s1 s2.
proof.
  move=> Us1 Us2 eq12; rewrite /perm_eq allP => x _ /=.
  by rewrite !count_uniq_mem 3:eq12 //; apply uniq_fst_uniq.
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

(* -------------------------------------------------------------------- *)
op map0 ['a,'b] = Self.oflist [<:'a * 'b>]
  axiomatized by map0E.

(* -------------------------------------------------------------------- *)
(* In PairList? *)
op get (xs : ('a * 'b) list) (a : 'a) =
  with xs = "[]"      => None
  with xs = (::) x xs => if a = x.`1
                         then Some x.`2
                         else get xs a.

lemma mem_get_uniq (xs : ('a * 'b) list) (a : 'a) (b : 'b):
  uniq_fst xs =>
  mem xs (a,b) <=> get xs a = Some b.
proof.
  elim xs=> //= [[a' b']] xs IH /= [].
  move=> a'_notin_fstxs uniq_xs; split.
    case=> [[-> ->] // | H].
    cut:= H => /mem_fst_mem; case (a = a')=> //= _ _.
    by rewrite -IH.
  case (a = a')=> //= [_ /someI // | ].
  by rewrite -IH.
qed.

lemma get_mem (xs : ('a * 'b) list) (x : 'a):
  get xs x <> None <=> mem xs (x,oget (get xs x)).
proof.
  by elim xs=> //= [[a b]] xs IH /=; case (x = a).
qed.

op "_.[_]" (m : ('a,'b) fmap) (x : 'a) = get (elems m) x
  axiomatized by getE.

lemma mapP (m1 m2 : ('a,'b) fmap):
  (m1 = m2) <=> (forall x, m1.[x] = m2.[x]).
proof.
  split=> [-> // | H]; apply fmap_eq; apply uniq_perm_eq;
    first 2 by apply uniq_fst_uniq; apply uniq_keys.
  move: H; rewrite getE /= => H [a b].
  by rewrite !mem_get_uniq 1..2:uniq_keys // H.
qed.

(* -------------------------------------------------------------------- *)
op dom (m : ('a,'b) fmap) = NewFSet.oflist (fst (elems m))
  axiomatized by domE.

lemma in_dom (m: ('a,'b) fmap) (a : 'a):
  mem (dom m) a <=> m.[a] <> None.
proof.
  rewrite domE getE /= mem_oflist.
  split.
    rewrite mem_fst_ex_snd=> [] b.
    by rewrite mem_get_uniq 1:uniq_keys // => ->.
  by rewrite get_mem=> /mem_fst_mem.
qed.

(* -------------------------------------------------------------------- *)
op rng (m : ('a,'b) fmap) = NewFSet.oflist (snd (elems m))
  axiomatized by rngE.

lemma in_rng (m: ('a,'b) fmap) (b : 'b):
  mem (rng m) b <=> (exists a, m.[a] = Some b).
proof.
  rewrite rngE getE /= mem_oflist.
  split.
    rewrite mem_snd_ex_fst=> [] a.
    by rewrite mem_get_uniq 1:uniq_keys // => a_in_m; exists a.
  by move=> [] a; rewrite -mem_get_uniq 1:uniq_keys // => /mem_snd_mem.
qed.

(* -------------------------------------------------------------------- *)
op size (m : ('a,'b) fmap) = card (dom m)
  axiomatized by sizeE.
