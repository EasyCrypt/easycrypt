(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

require import Fun Pred Option Pair Int NewList NewFSet.

pragma +implicits.

(* -------------------------------------------------------------------- *)
lemma perm_eq_uniq_map (f : 'a -> 'b)  (s1 s2 : 'a list):
  perm_eq s1 s2 => uniq (map f s1) <=> uniq (map f s2).
proof. by move=> /(perm_eq_map f) /perm_eq_uniq ->. qed.

lemma uniq_perm_eq_map (s1 s2 : ('a * 'b) list) (f: 'a * 'b -> 'c):
     uniq (map f s1) => uniq (map f s2)
  => (forall (x : 'a * 'b), mem s1 x <=> mem s2 x)
  => perm_eq s1 s2.
proof. by move=> /uniq_map h1 /uniq_map h2 /(uniq_perm_eq _ _ h1 h2). qed.

(* -------------------------------------------------------------------- *)
op augment (s : ('a * 'b) list) (kv : 'a * 'b) =
  if mem (map fst s) kv.`1 then s else rcons s kv.

lemma nosmt augment_nil (kv : 'a * 'b): augment [] kv = [kv].
proof. by []. qed.

lemma augmentP (s : ('a * 'b) list) x y:
     (  mem (map fst s) x /\ augment s (x, y) = s)
  \/ (! mem (map fst s) x /\ augment s (x, y) = rcons s (x, y)).
proof. by case: (mem (map fst s) x)=> //=; rewrite /augment => ->. qed.

op reduce (xs : ('a * 'b) list): ('a * 'b) list =
  foldl augment [] xs.

lemma reduce_nil: reduce [<:'a * 'b>] = [].
proof. by []. qed.

lemma nosmt reduce_cat (r s : ('a * 'b) list):
    foldl augment r s
  = r ++ filter (comp (predC (mem (map fst r))) fst) (foldl augment [] s).
proof.
  rewrite -@(revK s) !foldl_rev; pose f := fun x z => augment z x.
  elim/last_ind: s r => /=.
    by move=> r; rewrite !rev_nil /= cats0.
  move=> s [x y] ih r; rewrite !rev_rcons /= ih => {ih}.
  rewrite {1}/f {1}/augment map_cat mem_cat /=.
  pose t1 := map fst _; pose t2 := map fst _.
  case: (mem t1 x \/ mem t2 x) => //; last first.
    rewrite -nor => [t1_x t2_x]; rewrite rcons_cat; congr.
    rewrite {2}/f /augment /=; pose t := map fst _.
    case: (mem t x) => h; last first.
      by rewrite filter_rcons /= /comp /predC t1_x.
    have: mem t2 x; rewrite // /t2 /comp.
    have <- := filter_map<:'a, 'a * 'b> fst (predC (mem t1)).
    by rewrite mem_filter /predC t1_x.
  case=> h; congr; rewrite {2}/f /augment /=; last first.
    move: h; rewrite /t2 => /mapP [z] [h ->>].
    by move: h; rewrite mem_filter => [_ /(map_f fst) ->].
  case: (NewList.mem _ _) => //=; rewrite filter_rcons.
  by rewrite /comp /predC h.
qed.

lemma reduce_cons (x : 'a) (y : 'b) s:
    reduce ((x, y) :: s)
  = (x, y) :: filter (comp (predC1 x) fst) (reduce s).
proof. by rewrite {1}/reduce /= augment_nil reduce_cat cat1s. qed.

lemma assoc_reduce (s : ('a * 'b) list):
  forall x, assoc (reduce s) x = assoc s x.
proof. 
  move=> x; elim: s => //; case=> x' y' s ih.
  rewrite reduce_cons !assoc_cons; case: (x = x')=> //.
  by move=> ne_xx'; rewrite assoc_filter.
qed.

lemma dom_reduce (s : ('a * 'b) list):
  forall x, mem (map fst (reduce s)) x <=> mem (map fst s) x.
proof.
  move=> x; elim: s => [|[x' y] s ih] /=; 1: by rewrite reduce_nil.
  rewrite reduce_cons /=; apply/eq_iff/orb_id2l.
  rewrite {1}/fst /comp /= => ne_xx'.
  have <- := filter_map fst<:'a, 'b> (predC1 x').
  by rewrite mem_filter /predC1 ne_xx' /= ih.
qed.

lemma reduced_reduce (s : ('a * 'b) list): uniq (map fst (reduce s)).
proof.
  elim: s => [|[x y] s ih]; 1: by rewrite reduce_nil.
  rewrite reduce_cons /= {3}/fst /=; split.
    by apply/negP=> /mapP [[x' y']]; rewrite mem_filter=> [* h1 h2 ->>].
  rewrite /comp; have <- := filter_map fst<:'a, 'b> (predC1 x).
  by rewrite filter_uniq.
qed.

lemma reduce_reduced (s : ('a * 'b) list):
  uniq (map fst s) => reduce s = s.
proof.
  elim: s => [|[x y] s ih]; 1: by rewrite reduce_nil.
  rewrite reduce_cons /= {2}/fst /= => [x_notin_s /ih ->].
  (* FIXME: here, `congr` generates an invalid proof term *)
  rewrite @(eq_in_filter _ predT) ?filter_predT /predT //=.
  case=> x' y' /(map_f fst) x'_in_s; apply/negP => <<-.
  by move: x_notin_s.
qed.

lemma reduceK (xs : ('a * 'b) list): reduce (reduce xs) = reduce xs.
proof. by rewrite reduce_reduced 1:reduced_reduce. qed.

lemma mem_reduce_head (xs : ('a * 'b) list) a b:
  mem (reduce ((a, b) :: xs)) (a, b).
proof. by rewrite reduce_cons. qed.

(* -------------------------------------------------------------------- *)
(* Finite maps are abstractely represented as the quotient by           *)
(* [perm_eq] of lists of pairs without first projection duplicates.     *)

type ('a, 'b) fmap.

op elems  : ('a, 'b) fmap -> ('a * 'b) list.
op oflist : ('a * 'b) list -> ('a,'b) fmap.

axiom elemsK  (m : ('a, 'b) fmap) : Self.oflist (elems m) = m.
axiom oflistK (s : ('a * 'b) list): perm_eq (reduce s) (elems (Self.oflist s)).

lemma uniq_keys (m : ('a, 'b) fmap): uniq (map fst (elems m)).
proof.
  rewrite -elemsK; move: (elems m) => {m} m.
  apply @(perm_eq_uniq (map fst (reduce m)) _).
    by apply perm_eq_map; apply oflistK.
  by apply reduced_reduce.
qed.

axiom fmap_eq (s1 s2 : ('a,'b) fmap):
  (perm_eq (elems s1) (elems s2)) => (s1 = s2).

(* -------------------------------------------------------------------- *)
lemma fmapW (p : ('a, 'b) fmap -> bool):
     (forall m, uniq (map fst m) => p (Self.oflist m))
  => forall m, p m.
proof. by move=> ih m; rewrite -elemsK; apply/ih/uniq_keys. qed.

(* -------------------------------------------------------------------- *)
op "_.[_]" (m : ('a,'b) fmap) (x : 'a) = assoc (elems m) x
  axiomatized by getE.

lemma get_oflist (s : ('a * 'b) list):
  forall x, (Self.oflist s).[x] = assoc s x.
proof.
  move=> x; rewrite getE; rewrite -@(assoc_reduce s).
  apply/eq_sym/perm_eq_assoc; 1: by apply/uniq_keys.
  by apply/oflistK.
qed.

lemma fmapP (m1 m2 : ('a,'b) fmap):
  (m1 = m2) <=> (forall x, m1.[x] = m2.[x]).
proof.
  split=> // h; apply fmap_eq; apply uniq_perm_eq;
    first 2 by apply @(uniq_map fst); apply uniq_keys.
  case=> x y; move: (h x); rewrite !getE => {h} h.
  by rewrite !mem_assoc_uniq ?uniq_keys // h.
qed.

(* -------------------------------------------------------------------- *)
op "_.[_<-_]" (m : ('a, 'b) fmap) (a : 'a) (b : 'b) =
  Self.oflist (reduce ((a, b) :: elems m))
  axiomatized by setE.

(* -------------------------------------------------------------------- *)
op map0 ['a,'b] = Self.oflist [<:'a * 'b>] axiomatized by map0E.

lemma get0 x: (map0<:'a, 'b>).[x] = None.
proof. by rewrite map0E get_oflist. qed.

(* -------------------------------------------------------------------- *)
lemma get_set (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  m.[a <- b].[a] = Some b.
proof. by rewrite setE get_oflist assoc_reduce assoc_head. qed.

(* -------------------------------------------------------------------- *)
op dom ['a 'b] (m : ('a, 'b) fmap) =
  NewFSet.oflist (map fst (elems m))
  axiomatized by domE.

lemma dom_oflist (s : ('a * 'b) list):
  forall x, mem (dom (Self.oflist s)) x <=> mem (map fst s) x.
proof.
  move=> x; rewrite domE mem_oflist.
  have/perm_eq_sym/(perm_eq_map fst) := oflistK s.
  by move/perm_eq_mem=> ->; apply/dom_reduce.
qed.

lemma mem_domE (m : ('a, 'b) fmap) x:
  mem (dom m) x <=> mem (map fst (elems m)) x.
proof.
  elim/fmapW: m=> m _; rewrite dom_oflist; apply/perm_eq_mem.
  by apply/perm_eq_map; rewrite -{1}@(reduce_reduced m) // oflistK.
qed.

lemma dom0: dom map0<:'a, 'b> = set0.
proof. by apply/setP=> x; rewrite map0E dom_oflist in_set0. qed.

(* -------------------------------------------------------------------- *)
op rng ['a 'b] (m : ('a, 'b) fmap) = 
  NewFSet.oflist (map snd (elems m))
  axiomatized by rngE.

lemma in_rng (m: ('a,'b) fmap) (b : 'b):
  mem (rng m) b <=> (exists a, m.[a] = Some b).
proof.
  rewrite rngE mem_oflist; split.
    move/NewList.mapP=> [] [x y] [h ->]; exists x.
    by rewrite getE -mem_assoc_uniq // uniq_keys.
  case=> x; rewrite getE -mem_assoc_uniq ?uniq_keys // => h.
  by apply/NewList.mapP; exists (x, b).
qed.

(* -------------------------------------------------------------------- *)
op (+) (m1 m2 : ('a, 'b) fmap)
  = Self.oflist (elems m2 ++ elems m1)
  axiomatized by joinE.

lemma get_join (m1 m2 : ('a, 'b) fmap) x:
  (m1 + m2).[x] = if mem (dom m2) x then m2.[x] else m1.[x].
proof. by rewrite joinE get_oflist mem_domE assoc_cat -!getE. qed.

(* -------------------------------------------------------------------- *)
op size (m : ('a, 'b) fmap) = card (dom m)
  axiomatized by sizeE.
