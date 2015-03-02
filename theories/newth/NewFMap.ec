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
  by move=> ne_xx'; rewrite assoc_filter /predC1 ne_xx'.
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
op map0 ['a,'b] = Self.oflist [<:'a * 'b>] axiomatized by map0E.

lemma get0 x: (map0<:'a, 'b>).[x] = None.
proof. by rewrite map0E get_oflist. qed.

lemma get_eq0 (m : ('a,'b) fmap):
  (forall x, m.[x] = None) => m = map0.
proof. by move=> h; apply fmapP=> x; rewrite h get0. qed.

(* -------------------------------------------------------------------- *)
op "_.[_<-_]" (m : ('a, 'b) fmap) (a : 'a) (b : 'b) =
  Self.oflist (reduce ((a, b) :: elems m))
  axiomatized by setE.

lemma get_set (m : ('a, 'b) fmap) (a : 'a) (b : 'b) (x : 'a):
  m.[a <- b].[x] = if x = a then Some b else m.[x].
proof.
  rewrite setE get_oflist assoc_reduce assoc_cons getE;
    by case (x = a).
qed.

lemma get_set_eq (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  m.[a <- b].[a] = Some b.
proof. by rewrite get_set. qed.

lemma set_set (m : ('a,'b) fmap) x x' y y':
  forall a, m.[x <- y].[x' <- y'].[a] = if x = x' then m.[x' <- y'].[a]
                                        else m.[x' <- y'].[x <- y].[a].
proof.
  move=> a; case (x = x')=> [<<- {x'} | ne_x_x'].
    by rewrite !get_set; case (a = x).
  rewrite !get_set.
  by case (a = x')=> //; case (a = x)=> // ->;rewrite ne_x_x'.
qed.

lemma nosmt set_set_eq y (m : ('a, 'b) fmap) x y':
  forall a, m.[x <- y].[x <- y'].[a] = m.[x <- y'].[a].
proof. by move=> a; rewrite set_set. qed.

(* -------------------------------------------------------------------- *)
op rm (m : ('a, 'b) fmap) (a : 'a) =
  Self.oflist (filter (comp (predC1 a) fst) (elems m))
  axiomatized by rmE.

lemma get_rm (m : ('a, 'b) fmap) (a : 'a):
  forall x, (rm m a).[x] = if x = a then None else m.[x].
proof.
  move=> x; rewrite rmE get_oflist; case (x = a)=> [->> | ].
    by rewrite assoc_filter.
  by rewrite assoc_filter /predC1 getE=> ->.
qed.

lemma get_rm_eq (m : ('a,'b) fmap) (a : 'a): (rm m a).[a] = None.
proof. by rewrite get_rm. qed.

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
proof. by rewrite domE mem_oflist. qed.

lemma in_dom (m : ('a, 'b) fmap) x:
  mem (dom m) x <=> m.[x] <> None.
proof.
  rewrite mem_domE getE;
    by have [[-> [y [_ ->]]] | [-> ->]] := assocP (elems m) x.
qed.

lemma fmap_domP (m1 m2 : ('a, 'b) fmap):
  (m1 = m2) <=>    (forall x, mem (dom m1) x = mem (dom m2) x)
                /\ (forall x, mem (dom m1) x => m1.[x] = m2.[x]).
proof.
  split=> // [[]] eq_dom eq_on_dom.
  apply fmapP=> x; case (mem (dom m1) x)=> h.
    by apply eq_on_dom.
  have := h; move: h; rewrite {2}eq_dom !in_dom /=.
  by move=> -> ->.
qed.

lemma dom0: dom map0<:'a, 'b> = set0.
proof. by apply/setP=> x; rewrite map0E dom_oflist in_set0. qed.

lemma dom_eq0 (m : ('a,'b) fmap):
  dom m = set0 => m = map0.
proof.
  move=> eq_dom; apply fmap_domP; rewrite eq_dom dom0 //= => x;
    by rewrite in_set0.
qed.

lemma dom_set (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  forall x, mem (dom m.[a <- b]) x <=> mem (setU (dom m) (set1 a)) x.
proof.
  move=> x; rewrite in_setU in_set1 !in_dom get_set;
    by case (x = a).
qed.

lemma dom_set_eq (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  mem (dom m.[a <- b]) a.
proof. by rewrite dom_set in_setU in_set1. qed.

lemma dom_rm (m : ('a, 'b) fmap) (a : 'a):
  forall x, mem (dom (rm m a)) x <=> mem (setD (dom m) (set1 a)) x.
proof.
  by move=> x; rewrite in_setD in_set1 !in_dom get_rm; case (x = a).
qed.

lemma dom_rm_eq (m : ('a, 'b) fmap) (a : 'a): !mem (dom (rm m a)) a.
proof. by rewrite dom_rm in_setD in_set1. qed.

(* -------------------------------------------------------------------- *)
op rng ['a 'b] (m : ('a, 'b) fmap) = 
  NewFSet.oflist (map snd (elems m))
  axiomatized by rngE.

lemma mem_rngE (m : ('a, 'b) fmap) y:
  mem (rng m) y <=> mem (map snd (elems m)) y.
proof. by rewrite rngE mem_oflist. qed.

lemma in_rng (m: ('a,'b) fmap) (b : 'b):
  mem (rng m) b <=> (exists a, m.[a] = Some b).
proof.
  rewrite mem_rngE; split.
    move/NewList.mapP=> [] [x y] [h ->]; exists x.
    by rewrite getE -mem_assoc_uniq // uniq_keys.
  case=> x; rewrite getE -mem_assoc_uniq ?uniq_keys // => h.
  by apply/NewList.mapP; exists (x, b).
qed.

lemma rng0: rng map0<:'a, 'b> = set0.
proof.
  apply/setP=> x; rewrite in_set0 //= in_rng.
  (* FIXME: here, higher-order pattern-matching would help *)
  have //= -> // x' := nexists (fun (a:'a), map0.[a] = Some x).
  by rewrite get0.
qed.

lemma rng_set (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  forall y, mem (rng m.[a<-b]) y <=> mem (setU (rng (rm m a)) (set1 b)) y.
proof.
  move=> y; rewrite in_setU in_set1 !in_rng; split=> [[] x |].
    rewrite get_set; case (x = a)=> [->> /= <<- |].
      by right.
    by move=> ne_xa mx_y; left; exists x; rewrite get_rm ne_xa /=.
  rewrite orbC -ora_or=> [->> | ].
    by exists a; rewrite get_set_eq.
  move=> ne_yb [] x; rewrite get_rm.
  case (x = a)=> //= ne_xa <-.
  by exists x; rewrite get_set ne_xa.
qed.

lemma rng_set_eq (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  mem (rng m.[a<-b]) b.
proof. by rewrite rng_set in_setU in_set1. qed.

lemma rng_rm (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  mem (rng (rm m a)) b <=> (exists x, x <> a /\ m.[x] = Some b).
proof.
  rewrite in_rng; split.
    move=> [x]; rewrite get_rm; case (x = a)=> //=.
    by move=> ne_x_a mx_b; exists x.
  by move=> [x] [ne_x_a mx_b]; exists x; rewrite get_rm ne_x_a.
qed.

(* -------------------------------------------------------------------- *)
op has (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap) =
  NewList.has (fun (x : 'a * 'b), p x.`1 x.`2) (elems m)
  axiomatized by hasE.

op all (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap) =
  NewList.all (fun (x : 'a * 'b), p x.`1 x.`2) (elems m)
  axiomatized by allE.

lemma hasP p (m : ('a, 'b) fmap):
  has p m <=> (exists x, mem (dom m) x /\ p x (oget m.[x])).
proof.
  (** FIXME: rewriting under quantifiers would help here **)
  split.
    rewrite hasE hasP=> [[a b]] /= [ab_in_m] p_a_b.
    have:= ab_in_m; rewrite mem_assoc_uniq 1:uniq_keys // -getE => ma_b.
    exists a; rewrite ma_b mem_domE /oget /= p_a_b /= mem_map_fst;
      by exists b.
  move=> [a] [].
  rewrite mem_domE mem_map_fst=> [b] ab_in_m.
  have:= ab_in_m; rewrite mem_assoc_uniq 1:uniq_keys // getE /oget=> -> /= p_a_b.
  by rewrite hasE hasP; exists (a,b).
qed.

lemma allP p (m : ('a, 'b) fmap):
  all p m <=> (forall x, mem (dom m) x => p x (oget m.[x])).
proof.
  (** FIXME: rewriting under quantifiers would help here **)
  split.
    rewrite allE allP=> h a; rewrite mem_domE mem_map_fst=> [b] ab_in_m.
    have:= ab_in_m; rewrite mem_assoc_uniq 1:uniq_keys // -getE /oget => -> /=.
    by apply @(h (a,b)).
  move=> h.
  rewrite allE allP=> [a b] /= ab_in_m.
  rewrite (_: b = oget m.[a]).
    by move: ab_in_m; rewrite mem_assoc_uniq 1:uniq_keys // getE /oget=> ->.
  by apply h; rewrite mem_domE mem_map_fst; exists b.
qed.

(* -------------------------------------------------------------------- *)
op (+) (m1 m2 : ('a, 'b) fmap)
  = Self.oflist (elems m2 ++ elems m1)
  axiomatized by joinE.

lemma get_join (m1 m2 : ('a, 'b) fmap) x:
  (m1 + m2).[x] = if mem (dom m2) x then m2.[x] else m1.[x].
proof. by rewrite joinE get_oflist mem_domE assoc_cat -!getE. qed.

lemma dom_join (m1 m2 : ('a, 'b) fmap):
  forall x, mem (dom (m1 + m2)) x <=> mem (setU (dom m1) (dom m2)) x.
proof.
  by move=> x; rewrite in_setU !in_dom get_join in_dom; case (m2.[x]).
qed.

lemma has_join (p : 'a -> 'b -> bool) (m1 m2 : ('a, 'b) fmap):
  has p (m1 + m2) => has p m1 \/ has p m2.
proof.
  rewrite !hasP=> [x].
  rewrite get_join dom_join in_setU; case (mem (dom m2) x)=> //=.
    by move=> x_in_m2 p_x_m2x; right; exists x.
  by move=> h {h} [x_in_m1 p_x_m1x]; left; exists x.
qed.

lemma has_last_join (m1 m2 : ('a, 'b) fmap) (p : 'a -> 'b -> bool):
  has p m2 => has p (m1 + m2).
proof.
  rewrite !hasP=> [x] [x_in_m2 p_x_m2x].
  by exists x; rewrite dom_join get_join in_setU x_in_m2.
qed.

lemma has_join_precise (p : 'a -> 'b -> bool) (m1 m2 : ('a, 'b) fmap):
  has p (m1 + m2) <=> has p m2 \/ has (fun x (y : 'b) => p x y /\ !mem (dom m2) x) m1.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
op find (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap) =
  onth (map fst (elems m)) (find (fun (x : 'a * 'b), p x.`1 x.`2) (elems m))
  axiomatized by findE.

(** The following are inspired from lemmas on NewList.find.
    I'm not sure they are sufficient for maps. **)
lemma get_find (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap):
  has p m => p (oget (find p m)) (oget m.[oget (find p m)]).
proof. admit. qed.

lemma has_find (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap):
  has p m <=> mem (dom m) (oget (find p m)).
proof. admit. qed.

lemma find_none (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap):
  !has p m <=> find p m = None.
proof.
  rewrite hasE /= findE.
  rewrite NewList.has_find.
  split.
    by move=> h; rewrite onth_nth_map -map_comp nth_default 1:size_map 1:lezNgt.
  by apply absurd=> /= h; rewrite @(onth_nth witness) 1:smt.
qed.

lemma find_some (p:'a -> 'b -> bool) m x:
  find p m = Some x =>
  mem (dom m) x /\ p x (oget m.[x]).
proof. admit. qed.

(* -------------------------------------------------------------------- *)
op size (m : ('a, 'b) fmap) = card (dom m)
  axiomatized by sizeE.
