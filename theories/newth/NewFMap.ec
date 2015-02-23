(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

require import Fun Pred Option Pair Int NewList NewFSet.

pragma +implicits.

(** Even more general (to NewList?) **)
lemma uniq_map_uniq (xs : 'a list) (f : 'a -> 'c):
  uniq (map f xs) => uniq xs.
proof.
  elim xs=> //= x xs IH [] x1_notin_fxs /IH -> /=.
  rewrite -not_def=> x_in_xs; move: x1_notin_fxs=> //=. (* This is a weird way of contraposing *)
  by rewrite -has_pred1 has_map hasP; exists x.
qed.

lemma perm_eq_uniq_map (f : 'a -> 'b)  (s1 s2 : 'a list):
  perm_eq s1 s2 => uniq (map f s1) <=> uniq (map f s2).
proof. by move=> /(perm_eq_map f) /perm_eq_uniq ->. qed.

lemma uniq_perm_eq_map (s1 s2 : ('a * 'b) list) (f: 'a * 'b -> 'c):
  uniq (map f s1) =>
  uniq (map f s2) =>
  (forall (x : 'a * 'b), mem s1 x <=> mem s2 x) =>
  perm_eq s1 s2.
proof.
  move=> Us1 Us2 eq12; rewrite /perm_eq allP => x _ /=.
  by rewrite !count_uniq_mem 3:eq12 //; apply @(uniq_map_uniq _ f).
qed.

(* TODO: this may be of more general interest and may benefit from a
         move to NewList, or a separate PairList theory. *)
lemma mem_fst_ex_snd (xs : ('a * 'b) list) (x : 'a):
  mem (map fst xs) x <=> (exists y, mem xs (x,y)).
proof.
  rewrite -has_pred1 has_map hasP /preim/fst/pred1; split.
    by move=> [[a b]] /= [x0_in_xs ->>]; exists b.
  by move=> [y] xs_in_xs; exists (x,y).
qed.

lemma mem_snd_ex_fst (xs : ('a * 'b) list) (y : 'b):
  mem (map snd xs) y <=> (exists x, mem xs (x,y)).
proof.
  rewrite -has_pred1 has_map hasP /preim/snd/pred1; split.
    by move=> [[a b]] /= [x0_in_xs ->>]; exists a.
  by move=> [x] xs_in_xs; exists (x,y).
qed.

op reduce (xs : ('a * 'b) list): ('a * 'b) list =
  foldl (fun aout (kv : 'a * 'b) =>
           if mem (map fst aout) kv.`1 then aout else rcons aout kv)
        [] xs.

lemma mem_fst_reduce (xs : ('a * 'b) list):
  mem (map fst (reduce xs)) = mem (map fst xs).
proof.
  rewrite /reduce -{2}@(cats0 xs).
  move: [<:'a*'b>]; elim xs=> //= x xs IH acc.
  case (mem (map fst acc) x.`1)=> //= H.
    apply fun_ext=> a; rewrite IH {2}/fst in_cons map_cat mem_cat.
    by case (a = x.`1)=> [->> //= | //=]; rewrite H.
  apply fun_ext=> a; rewrite IH !(in_cons,map_cat,map_rcons,mem_cat,mem_rcons) {2 4}/fst /=; smt. (* sic *)
qed.

lemma uniq_fst_reduce (xs : ('a * 'b) list): uniq (map fst (reduce xs)).
proof.
  rewrite /reduce.
  cut: uniq (map fst [<:'a*'b>]) by done.
  move: [<:'a*'b>]; elim xs=> //= x xs IH acc uniq_fst_acc.
  case (mem (map fst acc) x.`1).
    by rewrite (IH acc).
  move=> x1_notin_map_fst_acc.
  by rewrite IH 1:map_rcons 1:rcons_uniq {2}/fst.
qed.

lemma reduce_uniq_fst (xs : ('a * 'b) list):
  uniq (map fst xs) =>
  reduce xs = xs.
proof.
  rewrite /reduce -{1 3}cat0s.
  move: [<:'a*'b>]; elim xs=> //=.
    by move=> acc; rewrite cats0.
  move=> x xs IH acc uniq_faccxxs.
  (* We could apply IH on the ite expression, but we'd eventually need
     to prove that one of the branches is stupid anyway. *)
  case (mem (map fst acc) x.`1)=> [x1_in_acc | x1_notin_acc].
    by rewrite IH //; move: uniq_faccxxs;
       rewrite !map_cat map_cons !cat_uniq /= x1_in_acc.
  by rewrite IH cat_rcons.
qed.

lemma reducess (xs : ('a * 'b) list): reduce (reduce xs) = reduce xs.
proof. by rewrite reduce_uniq_fst 1:uniq_fst_reduce. qed.

lemma mem_reduce_head (xs : ('a * 'b) list) a b: mem (reduce ((a,b)::xs)) (a,b).
proof.
  rewrite /reduce /=.
  cut: !mem [] (a,b) by done.
  move: [<:'a*'b>]; elim xs=> //= x xs IH acc ab_notin_acc.
  rewrite {2}/fst /=.
  case (x.`1 = a)=> //=.
    by rewrite IH.
  move=> x1_neq_a.
  case (mem (map fst acc) x.`1)=> //=.
    by rewrite IH.
  rewrite IH //.
  by rewrite mem_rcons in_cons eq_sym; move: x x1_neq_a=> [] /= x1 x2 ->.
qed.

(* -------------------------------------------------------------------- *)
(* Finite maps are abstractely represented as the quotient by
 * [perm_eq] of lists of pairs without first projection duplicates. *)

type ('a,'b) fmap.

op elems  : ('a,'b) fmap -> ('a * 'b) list.
op oflist : ('a * 'b) list -> ('a,'b) fmap.

axiom elemsK  (m : ('a,'b) fmap): Self.oflist (elems  m) = m.
axiom oflistK (s : ('a * 'b) list): perm_eq (reduce s) (elems (Self.oflist s)).

lemma uniq_keys (m : ('a,'b) fmap): uniq (map fst (elems m)).
proof.
  rewrite -elemsK; move: (elems m) => {m} m.
  apply @(perm_eq_uniq (map fst (reduce m)) _).
    by apply perm_eq_map; apply oflistK.
  by apply uniq_fst_reduce.
qed.

axiom fmap_eq (s1 s2 : ('a,'b) fmap):
  (perm_eq (elems s1) (elems s2)) => (s1 = s2).

(* -------------------------------------------------------------------- *)
op map0 ['a,'b] = Self.oflist [<:'a * 'b>]
  axiomatized by map0E.

(* -------------------------------------------------------------------- *)
(* In PairList? *)
op find (xs : ('a * 'b) list) (a : 'a) =
  omap snd (onth xs (index a (map fst xs))).

lemma find_mem (xs : ('a * 'b) list) (x : 'a):
  find xs x <> None <=> mem xs (x,oget (find xs x)).
proof.
  elim xs=> //= [[a b]] xs IH /=.
  case (x = a)=> //= [<<- | a_neq_r].
    by rewrite /find map_cons index_head onth_nth_map @(nth_map witness) /= 1:smt.
  rewrite /find map_cons index_cons {1}/fst /= a_neq_r /=.
  rewrite (_: index x (map fst xs) + 1 <> 0) //= 1:smt.
  by rewrite (_: forall x, x + 1 - 1 = x) 1:smt.
qed.

lemma mem_find_uniq (xs : ('a * 'b) list) (a : 'a) (b : 'b):
  uniq (map fst xs) =>
  mem xs (a,b) <=> find xs a = Some b.
proof.
  (** This feels larger than necessary **)
  elim xs=> //= [[a' b']] xs IH /= [] a'_notin_fstxs /IH {IH} IH.
  case (a = a')=> [->> /= | /= a_neq_a'].
    case (b = b')=> //= [->> | ].
      by rewrite /find map_cons index_head.
    rewrite /Self.find /snd map_cons index_head /= //=.
    move=> b_neq_b'; split.
      move=> a'b_in_xs; move: a'_notin_fstxs; rewrite {2}/fst /=.
      rewrite -has_pred1 has_map hasP.
      cut /= H /H {H} H := for_ex (fun x => !(mem xs x /\ preim fst (pred1 a') x)).
      by cut := H (a',b); rewrite a'b_in_xs.
    by move=> /someI ->>; move: b_neq_b'; rewrite -not_def.
  rewrite /find map_cons index_cons {1}/fst /= a_neq_a' /=.
  rewrite (_: index a (map fst xs) + 1 <> 0) //= 1:smt.
  rewrite (_: forall x, x + 1 - 1 = x) //= 1:smt.
  by rewrite -/(Self.find _ _) IH.
qed.

op "_.[_]" (m : ('a,'b) fmap) (x : 'a) = find (elems m) x
  axiomatized by getE.

lemma mapP (m1 m2 : ('a,'b) fmap):
  (m1 = m2) <=> (forall x, m1.[x] = m2.[x]).
proof.
  split=> // h; apply fmap_eq; apply uniq_perm_eq;
    first 2 by apply @(uniq_map_uniq _ fst); apply uniq_keys.
  case=> x y; move: (h x); rewrite !getE => {h} h.
  by rewrite !mem_find_uniq 1..2:uniq_keys // h.
qed.

(* -------------------------------------------------------------------- *)
op "_.[_<-_]" (m : ('a,'b) fmap) (a : 'a) (b : 'b) =
  Self.oflist (reduce ((a,b)::elems m))
axiomatized by setE.

lemma get_set (m : ('a,'b) fmap) (a : 'a) (b : 'b):
  m.[a <- b].[a] = Some b.
proof.
  rewrite getE /=.
  print mem_find_uniq.
  cut <- := mem_find_uniq(elems m.[a <- b]) a b _.
    by apply uniq_keys.
  rewrite setE /=.
  rewrite -@(perm_eq_mem (reduce ((a,b)::elems m))) 1:-{1}reducess 1:oflistK //.
  apply mem_reduce_head.
qed.

(* -------------------------------------------------------------------- *)
op dom (m : ('a,'b) fmap) = NewFSet.oflist (map fst (elems m))
  axiomatized by domE.

lemma in_dom (m: ('a,'b) fmap) (a : 'a):
  mem (dom m) a <=> m.[a] <> None.
proof.
  rewrite domE getE /= mem_oflist.
  split.
    rewrite mem_fst_ex_snd=> [] b.
    by rewrite mem_find_uniq 1:uniq_keys // => ->.
  by rewrite find_mem=> H; rewrite -has_pred1 has_map hasP; exists (a,oget (find (elems m) a)).
qed.

(* -------------------------------------------------------------------- *)
op rng (m : ('a,'b) fmap) = NewFSet.oflist (map snd (elems m))
  axiomatized by rngE.

lemma in_rng (m: ('a,'b) fmap) (b : 'b):
  mem (rng m) b <=> (exists a, m.[a] = Some b).
proof.
  rewrite rngE mem_oflist; split.
    move/NewList.mapP=> [] [x y] [h ->]; exists x.
    by rewrite getE -mem_find_uniq // uniq_keys.
  case=> x; rewrite getE -mem_find_uniq ?uniq_keys // => h.
  by apply/NewList.mapP; exists (x, b).
qed.

(* -------------------------------------------------------------------- *)
op size (m : ('a,'b) fmap) = card (dom m)
  axiomatized by sizeE.
