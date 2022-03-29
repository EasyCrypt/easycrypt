(* -------------------------------------------------------------------- *)
require import AllCore Int List FSet.

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
  = r ++ filter (predC (mem (map fst r)) \o fst) (foldl augment [] s).
proof.
rewrite -(@revK s) !foldl_rev; pose f := fun x z => augment z x.
elim/last_ind: s r => /=.
  by move=> r; rewrite !rev_nil /= cats0.
move=> s [x y] ih r; rewrite !rev_rcons /= ih => {ih}.
rewrite {1}/f {1}/augment map_cat mem_cat /=.
pose t1 := map fst _; pose t2 := map fst _.
case: (mem t1 x \/ mem t2 x) => //; last first.
  rewrite negb_or => -[t1_x t2_x]; rewrite rcons_cat; congr.
  rewrite {2}/f /augment /=; pose t := map fst _.
  case: (mem t x) => h; last first.
    by rewrite filter_rcons /= /(\o) /predC t1_x.
  have: mem t2 x; rewrite // /t2 /(\o).
  have <- := filter_map<:'a, 'a * 'b> fst (predC (mem t1)).
  by rewrite mem_filter /predC t1_x.
case=> h; congr; rewrite {2}/f /augment /=; last first.
  move: h; rewrite /t2 => /mapP [z] [h ->>].
  by move: h; rewrite mem_filter => -[_ /(map_f fst) ->].
case: (List.mem _ _) => //=; rewrite filter_rcons.
by rewrite /(\o) /predC h.
qed.

lemma reduce_cons (x : 'a) (y : 'b) s:
    reduce ((x, y) :: s)
  = (x, y) :: filter (predC1 x \o fst) (reduce s).
proof. by rewrite {1}/reduce /= augment_nil reduce_cat cat1s. qed.

lemma assoc_reduce (s : ('a * 'b) list):
  forall x, assoc (reduce s) x = assoc s x.
proof.
move=> x; elim: s => //; case=> x' y' s ih.
rewrite reduce_cons !assoc_cons; case: (x = x')=> // ne_xx'.
by rewrite assoc_filter /predC1 ne_xx'.
qed.

lemma dom_reduce (s : ('a * 'b) list):
  forall x, mem (map fst (reduce s)) x <=> mem (map fst s) x.
proof.
move=> x; elim: s => [|[x' y] s ih] /=; 1: by rewrite reduce_nil.
rewrite reduce_cons /=; apply/orb_id2l.
rewrite /(\o) /= => ne_xx'.
by rewrite -(@filter_map _ (predC1 x')) mem_filter /predC1 ne_xx' /= ih.
qed.

lemma reduced_reduce (s : ('a * 'b) list): uniq (map fst (reduce s)).
proof.
elim: s => [|[x y] s ih]; 1: by rewrite reduce_nil.
rewrite reduce_cons /= ; split.
+ by apply/negP=> /mapP [[x' y']]; rewrite mem_filter=> -[# h1 h2 ->>].
rewrite /(\o); have <- := filter_map fst<:'a, 'b> (predC1 x).
by rewrite filter_uniq.
qed.

lemma reduce_reduced (s : ('a * 'b) list):
  uniq (map fst s) => reduce s = s.
proof.
elim: s => [|[x y] s ih]; 1: by rewrite reduce_nil.
rewrite reduce_cons /= => -[x_notin_s /ih ->].
rewrite (@eq_in_filter _ predT) ?filter_predT /predT //=.
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
apply (@perm_eq_uniq (map fst (reduce m)) _).
+ by apply perm_eq_map; apply oflistK.
by apply reduced_reduce.
qed.

axiom fmap_eq (s1 s2 : ('a,'b) fmap):
  (perm_eq (elems s1) (elems s2)) <=> (s1 = s2).

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
move=> x; rewrite getE; rewrite -(@assoc_reduce s).
apply/eq_sym/perm_eq_assoc; 1: by apply/uniq_keys.
by apply/oflistK.
qed.

lemma fmapP (m1 m2 : ('a,'b) fmap):
  (m1 = m2) <=> (forall x, m1.[x] = m2.[x]).
proof.
split=> // h; apply/fmap_eq/uniq_perm_eq; ~3:by apply/(@uniq_map fst)/uniq_keys.
case=> x y; move: (h x); rewrite !getE => {h} h.
by rewrite !mem_assoc_uniq ?uniq_keys // h.
qed.

(* -------------------------------------------------------------------- *)
op map0 ['a,'b] = Self.oflist [<:'a * 'b>] axiomatized by map0E.

(* -------------------------------------------------------------------- *)
op "_.[_<-_]" (m : ('a, 'b) fmap) (a : 'a) (b : 'b) =
  Self.oflist (reduce ((a, b) :: elems m))
  axiomatized by setE.

lemma getP (m : ('a, 'b) fmap) (a : 'a) (b : 'b) (x : 'a):
  m.[a <- b].[x] = if x = a then Some b else m.[x].
proof.
by rewrite setE get_oflist assoc_reduce assoc_cons getE; case: (x = a).
qed.

lemma getP_eq (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  m.[a <- b].[a] = Some b.
proof. by rewrite getP. qed.

lemma getP_neq (m : ('a, 'b) fmap) (a1 a2 : 'a) (b : 'b):
  a1 <> a2 =>
  m.[a1 <- b].[a2] = m.[a2].
proof. by rewrite getP eq_sym=> ->. qed.

lemma set_set (m : ('a,'b) fmap) x x' y y':
   m.[x <- y].[x' <- y'] = if x = x' then m.[x' <- y']
                           else m.[x' <- y'].[x <- y].
proof.
rewrite fmapP=> a; case (x = x')=> [<<- {x'} | ne_x_x']; rewrite !getP.
+ by case (a = x).
by case (a = x')=> //; case (a = x)=> // ->;rewrite ne_x_x'.
qed.

lemma nosmt set_set_eq y (m : ('a, 'b) fmap) x y':
  m.[x <- y].[x <- y'] = m.[x <- y'].
proof. by rewrite fmapP=> a; rewrite set_set. qed.

(* -------------------------------------------------------------------- *)
op rem (a : 'a) (m : ('a, 'b) fmap) =
  Self.oflist (filter (predC1 a \o fst) (elems m))
  axiomatized by remE.

lemma remP (a : 'a) (m : ('a, 'b) fmap):
  forall x, (rem a m).[x] = if x = a then None else m.[x].
proof.
move=> x; rewrite remE get_oflist assoc_filter; case (x = a)=> //=.
by rewrite /predC1 getE=> ->.
qed.

(* -------------------------------------------------------------------- *)
op dom ['a 'b] (m : ('a, 'b) fmap) =
  FSet.oflist (map fst (elems m))
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
rewrite mem_domE getE.
by case: (assocP (elems m) x)=> [[-> [y [_ ->]]] | [-> ->]].
qed.

lemma fmap_domP (m1 m2 : ('a, 'b) fmap):
  (m1 = m2) <=>    (forall x, mem (dom m1) x = mem (dom m2) x)
                /\ (forall x, mem (dom m1) x => m1.[x] = m2.[x]).
proof.
split=> // [[]] eq_dom eq_on_dom.
apply fmapP=> x; case: (mem (dom m1) x).
+ by apply eq_on_dom.
move=> ^; rewrite {2}eq_dom !in_dom /=.
by move=> -> ->.
qed.

lemma get_oget (m:('a,'b)fmap) (x:'a) :
    mem (dom m) x => m.[x] = Some (oget m.[x]).
proof. by rewrite in_dom; case: (m.[x]). qed.

(* -------------------------------------------------------------------- *)
op rng ['a 'b] (m : ('a, 'b) fmap) =
  FSet.oflist (map snd (elems m))
  axiomatized by rngE.

lemma mem_rngE (m : ('a, 'b) fmap) y:
  mem (rng m) y <=> mem (map snd (elems m)) y.
proof. by rewrite rngE mem_oflist. qed.

lemma in_rng (m: ('a,'b) fmap) (b : 'b):
  mem (rng m) b <=> (exists a, m.[a] = Some b).
proof.
rewrite mem_rngE; split.
+ move/List.mapP=> [] [x y] [h ->]; exists x.
  by rewrite getE -mem_assoc_uniq 1:uniq_keys.
case=> x; rewrite getE -mem_assoc_uniq ?uniq_keys // => h.
by apply/List.mapP; exists (x, b).
qed.

(* -------------------------------------------------------------------- *)
op has (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap) =
  List.has (fun (x : 'a * 'b), p x.`1 x.`2) (elems m)
  axiomatized by hasE.

lemma hasP p (m : ('a, 'b) fmap):
  has p m <=> (exists x, mem (dom m) x /\ p x (oget m.[x])).
proof.
rewrite hasE hasP /=; split=> [[[a b]] /= [^ab_in_m+ p_a_b] |[a] []].
+ rewrite mem_assoc_uniq 1:uniq_keys // -getE => ma_b.
  by exists a; rewrite ma_b mem_domE /oget /= p_a_b /= mem_map_fst; exists b.
rewrite mem_domE mem_map_fst=> -[b] ^ab_in_m+.
by rewrite mem_assoc_uniq 1:uniq_keys // getE /oget=> -> /= p_a_b; exists (a,b).
qed.

(* FIXME: name *)
lemma has_le p' (m : ('a, 'b) fmap) (p : 'a -> 'b -> bool):
  (forall x y, mem (dom m) x /\ p x y => mem (dom m) x /\ p' x y) =>
  has p  m =>
  has p' m.
proof.
by move=> le_p_p'; rewrite !hasP=> -[x] /le_p_p' [p'_x x_in_m]; exists x.
qed.

(* -------------------------------------------------------------------- *)
op all (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap) =
  List.all (fun (x : 'a * 'b), p x.`1 x.`2) (elems m)
  axiomatized by allE.

lemma allP p (m : ('a, 'b) fmap):
  all p m <=> (forall x, mem (dom m) x => p x (oget m.[x])).
proof.
rewrite allE allP; split=> [h a|h [a b] /= ^ab_in_m].
+ rewrite mem_domE mem_map_fst=> -[b] ^ab_in_m+.
  by rewrite mem_assoc_uniq 1:uniq_keys -getE /oget=> ->; apply (@h (a,b)).
rewrite mem_assoc_uniq 1:uniq_keys -getE=> /(@congr1 oget) <-.
by apply/h; rewrite mem_domE mem_map_fst; exists b.
qed.

lemma all_le p' (m : ('a, 'b) fmap) (p : 'a -> 'b -> bool):
  (forall x y, mem (dom m) x /\ p x y => mem (dom m) x /\ p' x y) =>
  all p  m =>
  all p' m.
proof.
move=> le_p_p'. rewrite !allP=> h x ^x_in_m /h p_x.
exact/(andWr _ (:@le_p_p' x (oget m.[x]) _)).
qed.

(* -------------------------------------------------------------------- *)
lemma has_all (m : ('a, 'b) fmap) (p : 'a -> 'b -> bool):
  has p m <=> !all (fun x y, !p x y) m.
proof.
rewrite hasP allP negb_forall /=; split=> [[x] [x_in_m p_x]|[] x].
+ by exists x; rewrite p_x.
by rewrite negb_imply /= => h; exists x.
qed.

(* -------------------------------------------------------------------- *)
op (+) (m1 m2 : ('a, 'b) fmap) = Self.oflist (elems m2 ++ elems m1)
  axiomatized by joinE.

lemma joinP (m1 m2 : ('a, 'b) fmap) x:
  (m1 + m2).[x] = if mem (dom m2) x then m2.[x] else m1.[x].
proof. by rewrite joinE get_oflist mem_domE assoc_cat -!getE. qed.

(* -------------------------------------------------------------------- *)
op find (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap) =
  onth (map fst (elems m)) (find (fun (x : 'a * 'b), p x.`1 x.`2) (elems m))
  axiomatized by findE.

(** The following are inspired from lemmas on List.find. findP is a
    total characterization, but a more usable interface may be useful. **)
lemma find_none (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap):
  has p m <=> find p m <> None.
proof.
rewrite hasE /= findE List.has_find; split=> [h|].
+ by rewrite (@onth_nth witness) 1:find_ge0/= 1:size_map.
by apply/contraLR=> h; rewrite onth_nth_map -map_comp nth_default 1:size_map 1:lezNgt.
qed.

lemma findP (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap):
     (exists x, find p m = Some x /\ mem (dom m) x /\ p x (oget m.[x]))
  \/ (find p m = None /\ forall x, mem (dom m) x => !p x (oget m.[x])).
proof.
case: (has p m)=> [^has_p | ^all_not_p].
+ rewrite hasE has_find.
  have:= find_ge0 (fun (x : 'a * 'b) => p x.`1 x.`2) (elems m).
  pose i:= find _ (elems m); move => le0_i lt_i_sizem; left.
  exists (nth witness (map ofst (elems m)) i); split.
  + by rewrite findE -/i (@onth_nth witness) 1:size_map.
  split.
  + by rewrite mem_domE -index_mem index_uniq 1,3:size_map 2:uniq_keys.
  have /= := nth_find witness (fun (x : 'a * 'b) => p (ofst x) (osnd x)) (elems m) _.
  + by rewrite -hasE.
  rewrite -/i -(@nth_map _ witness) // getE /assoc
          (@index_uniq witness i (map fst (elems m))).
  + by rewrite size_map.
  + exact/uniq_keys.
  by rewrite (@onth_nth witness) //.
rewrite has_all /= allP /= => h; right.
by split=> //; move: all_not_p; rewrite find_none.
qed.

(* -------------------------------------------------------------------- *)
op filter (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap) =
  oflist (filter (fun (x : 'a * 'b) => p x.`1 x.`2) (elems m))
  axiomatized by filterE.

(* FIXME: Move me *)
lemma filter_mem_map (p : 'a -> bool) (f : 'a -> 'b) (s : 'a list) x':
  mem (map f (filter p s)) x' => mem (map f s) x'.
proof. by elim s=> //= x xs ih; case (p x)=> [_ [//= |] | _] /ih ->. qed.

(* FIXME: Move me *)
lemma uniq_map_filter (p : 'a -> bool) (f : 'a -> 'b) (s : 'a list):
  uniq (map f s) => uniq (map f (filter p s)).
proof.
  elim s=> //= x xs ih [fx_notin_fxs uniq_fxs].
  by case (p x); rewrite ih //= -negP => h {h} /filter_mem_map.
qed.

lemma perm_eq_elems_filter (m : ('a, 'b) fmap) (p: 'a -> 'b -> bool):
  perm_eq (filter (fun (x : 'a * 'b) => p x.`1 x.`2) (elems m))
          (elems (filter p m)).
proof.
  (* FIXME: curry-uncurry should probably go into Pair for some chosen arities *)
  rewrite filterE; pose P:= fun (x : 'a * 'b) => p x.`1 x.`2.
  apply (perm_eq_trans _ _ (:@oflistK _)).
  rewrite reduce_reduced 2:perm_eq_refl //.
  by apply/uniq_map_filter/uniq_keys.
qed.

lemma mem_elems_filter (m : ('a, 'b) fmap) (p: 'a -> 'b -> bool) x y:
      mem (filter (fun (x : 'a * 'b) => p x.`1 x.`2) (elems m)) (x,y)
  <=> mem (elems (filter p m)) (x,y).
proof. by apply/perm_eq_mem/perm_eq_elems_filter. qed.

lemma mem_map_filter_elems (p : 'a -> 'b -> bool) (f : ('a * 'b) -> 'c) (m : ('a, 'b) fmap) a:
      mem (map f (filter (fun (x : 'a * 'b) => p x.`1 x.`2) (elems m))) a
  <=> mem (map f (elems (filter p m))) a.
proof. by apply/perm_eq_mem/perm_eq_map/perm_eq_elems_filter. qed.

lemma assoc_elems_filter (m : ('a, 'b) fmap) (p: 'a -> 'b -> bool) x:
    assoc (filter (fun (x : 'a * 'b) => p x.`1 x.`2) (elems m)) x
  = assoc (elems (filter p m)) x.
proof. by apply/perm_eq_assoc/perm_eq_elems_filter/uniq_keys. qed.

lemma dom_filter (p : 'a -> 'b -> bool) (m : ('a,'b) fmap) x:
  mem (dom (filter p m)) x <=> mem (dom m) x /\ p x (oget m.[x]).
proof.
  (* FIXME: curry-uncurry should probably go into Pair for some chosen arities *)
  pose P := fun (x : 'a * 'b) => p x.`1 x.`2.
  rewrite !mem_domE !mem_map_fst; split=> [[y] | [[y] xy_in_m]].
    rewrite -mem_elems_filter mem_filter getE /= => -[p_x_y xy_in_pm].
    split; 1:by exists y.
    by move: xy_in_pm; rewrite mem_assoc_uniq 1:uniq_keys // => ->.
  have:= xy_in_m; rewrite mem_assoc_uniq 1:uniq_keys // getE /oget=> -> /= p_x_y.
  by exists y; rewrite -mem_elems_filter mem_filter.
qed.

lemma filterP (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap) x:
  (filter p m).[x] = if   mem (dom m) x /\ p x (oget m.[x])
                     then m.[x]
                     else None.
proof.
  case (mem (dom m) x /\ p x (oget m.[x])); rewrite -dom_filter in_dom //=.
  case {-1}((filter p m).[x]) (eq_refl (filter p m).[x])=> //= y.
  rewrite getE -mem_assoc_uniq 1:uniq_keys //.
  rewrite -mem_elems_filter mem_filter /= mem_assoc_uniq 1:uniq_keys //.
  by rewrite getE=> -[_ ->].
qed.

lemma filter_eq_dom (m:('a,'b)fmap) (p1 p2:'a->'b->bool):
   (forall a, mem (dom m) a=> p1 a (oget m.[a]) = p2 a (oget m.[a])) =>
   filter p1 m = filter p2 m.
proof.
  by move=> Hp;apply fmapP=>z;rewrite !filterP;case (mem (dom m) z)=>// Hz;rewrite Hp.
qed.

lemma filter_eq (m:('a,'b)fmap) (p1 p2:'a->'b->bool):
   (forall a b, p1 a b = p2 a b) =>
   filter p1 m = filter p2 m.
proof. by move=>Hp;apply filter_eq_dom=>?_;apply Hp. qed.

lemma filter_dom (m : ('a,'b) fmap) (p : 'a -> 'b -> bool):
  filter (relI p (fun a (_ : 'b)=> mem (dom m) a)) m = filter p m.
proof. by apply/filter_eq_dom=> a @/relI ->. qed.

(* -------------------------------------------------------------------- *)
op map (f : 'a -> 'b -> 'c) (m : ('a, 'b) fmap) =
  oflist (map (fun (x : 'a * 'b) => (x.`1,f x.`1 x.`2)) (elems m))
  axiomatized by mapE.

lemma dom_map (m : ('a,'b) fmap) (f : 'a -> 'b -> 'c) x:
  mem (dom (map f m)) x <=> mem (dom m) x.
proof.
  rewrite mapE dom_oflist domE mem_oflist.
  by elim (elems m)=> //= [[a b] l] /= ->.
qed.

lemma perm_eq_elems_map (m : ('a, 'b) fmap) (f : 'a -> 'b -> 'c):
  perm_eq (map (fun (x : 'a * 'b) => (x.`1,f x.`1 x.`2)) (elems m))
          (elems (map f m)).
proof.
  pose F := fun (x : 'a * 'b) => (x.`1,f x.`1 x.`2).
  apply (@perm_eq_trans (reduce (map F (elems m)))).
    rewrite -{1}(@reduce_reduced (map F (elems m))) 2:perm_eq_refl //.
    have ->: forall s, map fst (map F s) = map fst s by elim.
    exact/uniq_keys.
  by rewrite mapE; apply/oflistK.
qed.

lemma mem_elems_map (m : ('a, 'b) fmap) (f : 'a -> 'b -> 'c) x y:
      mem (map (fun (x : 'a * 'b) => (x.`1,f x.`1 x.`2)) (elems m)) (x,y)
  <=> mem (elems (map f m)) (x,y).
proof. by apply/perm_eq_mem/perm_eq_elems_map. qed.

lemma mapP (f : 'a -> 'b -> 'c) (m : ('a, 'b) fmap) x:
  (map f m).[x] = omap (f x) m.[x].
proof.
  pose F := fun (x : 'a * 'b) => (x.`1,f x.`1 x.`2).
  case (mem (dom (map f m)) x)=> h //=.
    case {-1}((map f m).[x]) (eq_refl (map f m).[x])=> [nh | y].
      by move: h; rewrite in_dom nh.
    rewrite getE -mem_assoc_uniq 1:uniq_keys// -mem_elems_map mapP=> -[[a b]] /=.
    by rewrite mem_assoc_uniq 1:uniq_keys// -getE andbC=> -[[<<- ->>]] ->.
  have:= h; rewrite dom_map=> h'.
  by move: h h'; rewrite !in_dom /= => -> ->.
qed.

(* -------------------------------------------------------------------- *)
op eq_except (m1 m2 : ('a, 'b) fmap) (X : 'a -> bool) =
    filter (fun x y => !X x) m1
  = filter (fun x y => !X x) m2
  axiomatized by eq_exceptE.

lemma eq_except_refl (m : ('a, 'b) fmap) X: eq_except m m X.
proof. by rewrite eq_exceptE. qed.

lemma eq_except_sym (m1 m2 : ('a, 'b) fmap) X:
  eq_except m1 m2 X <=> eq_except m2 m1 X.
proof. by rewrite eq_exceptE eq_sym -eq_exceptE. qed.

lemma eq_except_trans (m2 m1 m3 : ('a, 'b) fmap) X:
  eq_except m1 m2 X =>
  eq_except m2 m3 X =>
  eq_except m1 m3 X.
proof. by rewrite !eq_exceptE; apply eq_trans. qed.

lemma eq_exceptP (m1 m2 : ('a, 'b) fmap) X:
  eq_except m1 m2 X <=>
  (forall x, !X x => m1.[x] = m2.[x]).
proof.
  rewrite eq_exceptE fmapP; split=> h x.
    move=> x_notin_X; have:= h x; rewrite !filterP /= x_notin_X /=.
    case (mem (dom m1) x); case (mem (dom m2) x); rewrite !in_dom=> //=.
    (* FIXME: Should the following two be dealt with by `trivial'? *)
      by rewrite eq_sym.
    by move=> -> ->.
  by rewrite !filterP /=; case (X x)=> //= /h; rewrite !in_dom=> ->.
qed.

(* -------------------------------------------------------------------- *)
op size (m : ('a, 'b) fmap) = card (dom m)
  axiomatized by sizeE.

(* -------------------------------------------------------------------- *)
(* TODO: Do we need unary variants of has, all, find and map?           *)

(* -------------------------------------------------------------------- *)
lemma map0P x: (map0<:'a, 'b>).[x] = None.
proof. by rewrite map0E get_oflist. qed.

lemma map0_eq0 (m : ('a,'b) fmap):
  (forall x, m.[x] = None) => m = map0.
proof. by move=> h; apply fmapP=> x; rewrite h map0P. qed.

lemma remP_eq (a : 'a) (m : ('a,'b) fmap): (rem a m).[a] = None.
proof. by rewrite remP. qed.

lemma rem_rem (a : 'a) (m : ('a, 'b) fmap):
  rem a (rem a m) = rem a m.
proof. by rewrite fmapP=> x; rewrite !remP; case (x = a). qed.

lemma dom0: dom map0<:'a, 'b> = fset0.
proof. by apply/fsetP=> x; rewrite map0E dom_oflist in_fset0. qed.

lemma dom_eq0 (m : ('a,'b) fmap):
  dom m = fset0 => m = map0.
proof.
  move=> eq_dom; apply fmap_domP; rewrite eq_dom dom0 //= => x;
    by rewrite in_fset0.
qed.

lemma domP (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  forall x, mem (dom m.[a <- b]) x <=> mem (dom m `|` fset1 a) x.
proof.
  move=> x; rewrite in_fsetU in_fset1 !in_dom getP;
    by case (x = a).
qed.

lemma domP_eq (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  mem (dom m.[a <- b]) a.
proof. by rewrite domP in_fsetU in_fset1. qed.

lemma dom_set (m:('a,'b) fmap) a b :
  dom m.[a<-b] = dom m `|` fset1 a.
proof. by apply/fsetP/domP. qed.

lemma dom_rem (a : 'a) (m : ('a, 'b) fmap):
  dom (rem a m) = dom m `\` fset1 a.
proof.
  by rewrite fsetP=> x; rewrite in_fsetD in_fset1 !in_dom remP; case (x = a).
qed.

lemma dom_rem_eq (a : 'a) (m : ('a, 'b) fmap): !mem (dom (rem a m)) a.
proof. by rewrite dom_rem in_fsetD in_fset1. qed.

lemma rng0: rng map0<:'a, 'b> = fset0.
proof.
  apply/fsetP=> x; rewrite in_fset0 //= in_rng.
  by rewrite negb_exists => a; rewrite /= map0P.
qed.

lemma find_set (m:('a,'b) fmap) y x (p:'a -> 'b -> bool):
  (forall x, mem (dom m) x => !p x (oget m.[x])) =>
  find p m.[x <- y] = if p x y then Some x else None.
proof.
  have [[a []->[]] | []-> Hp Hnp]:= findP p (m.[x<-y]);1: rewrite getP dom_set !inE /#.
  by case (p x y)=> //; have := Hp x;rewrite getP dom_set !inE.
qed.

lemma rng_set (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
      rng m.[a<-b] = rng (rem a m) `|` fset1 b.
proof.
  rewrite fsetP=> y; rewrite in_fsetU in_fset1 !in_rng; split=> [[] x |].
    rewrite getP; case (x = a)=> [->> /= <<- |ne_xa mx_y]; [right=> // |left].
    by exists x; rewrite remP ne_xa /=.
  rewrite orbC -oraE=> -[->> | ].
    by exists a; rewrite getP_eq.
  move=> ne_yb [] x; rewrite remP.
  case (x = a)=> //= ne_xa <-.
  by exists x; rewrite getP ne_xa.
qed.

lemma rng_set_eq (m : ('a, 'b) fmap) (a : 'a) (b : 'b):
  mem (rng m.[a<-b]) b.
proof. by rewrite rng_set in_fsetU in_fset1. qed.

lemma rng_rem (a : 'a) (m : ('a, 'b) fmap) (b : 'b):
  mem (rng (rem a m)) b <=> (exists x, x <> a /\ m.[x] = Some b).
proof.
  rewrite in_rng; split=> [[x]|[x] [ne_x_a mx_b]].
    rewrite remP; case (x = a)=> //=.
    by move=> ne_x_a mx_b; exists x.
  by exists x; rewrite remP ne_x_a.
qed.

lemma dom_join (m1 m2 : ('a, 'b) fmap):
  forall x, mem (dom (m1 + m2)) x <=> mem (dom m1 `|` dom m2) x.
proof.
  by move=> x; rewrite in_fsetU !in_dom joinP in_dom; case (m2.[x]).
qed.

lemma has_join (p : 'a -> 'b -> bool) (m1 m2 : ('a, 'b) fmap):
  has p (m1 + m2) <=> has (fun x y => p x y /\ !mem (dom m2) x) m1 \/ has p m2.
proof.
rewrite !hasP; split=> [[x]|].
  rewrite joinP dom_join in_fsetU.
  by case: (mem (dom m2) x)=> //=
       [x_in_m2 p_x_m2x|x_notin_m2 [x_in_m1 p_x_m1x]];
       [right|left]; exists x.
by move=> [[]|[]] x /> => [x_in_m1|h] p_x => [h|]; exists x; rewrite dom_join joinP in_fsetU h.
qed.

lemma get_find (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap):
  has p m => p (oget (find p m)) (oget m.[oget (find p m)]).
proof. by rewrite find_none; have:= findP p m; case (find p m). qed.

lemma has_find (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap):
  has p m <=> exists x, find p m  = Some x /\ mem (dom m) x.
proof.
  rewrite find_none; have:= findP p m.
  by case (find p m)=> //= x [x'] [eq_xx' [x'_in_m _]]; exists x'.
qed.

lemma find_some (p:'a -> 'b -> bool) m x:
  find p m = Some x =>
  mem (dom m) x /\ p x (oget m.[x]).
proof. by have:= findP p m; case (find p m). qed.

lemma rem_filter (m : ('a, 'b) fmap) x:
  rem x m = filter (fun x' y => x' <> x) m.
proof.
  apply fmapP=> x'; rewrite remP filterP; case (mem (dom m) x').
    by case (x' = x).
  by rewrite in_dom /= => ->.
qed.

lemma filter_predI (p1 p2: 'a -> 'b -> bool) (m : ('a, 'b) fmap):
  filter (fun a b => p1 a b /\ p2 a b) m = filter p1 (filter p2 m).
proof. by rewrite fmapP=>x;rewrite !(filterP, dom_filter)/#. qed.

lemma filter_filter (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap):
  filter p (filter p m) = filter p m.
proof. by rewrite -filter_predI;apply filter_eq => /#. qed.

lemma filter_rem (p:'a->'b->bool) (m:('a,'b)fmap) x:
  filter p (rem x m) = rem x (filter p m).
proof. rewrite !rem_filter -!filter_predI;apply filter_eq=>/#. qed.

lemma join_filter (p : 'a -> 'b -> bool) (m : ('a, 'b) fmap):
  (filter p m) + (filter (fun x y=> !p x y) m) = m.
proof.
  rewrite fmapP=> x; rewrite joinP dom_filter /= !filterP.
  case (mem (dom m) x)=> /=.
    by case (p x (oget m.[x])).
  by rewrite in_dom /= eq_sym.
qed.

lemma eq_except_set a b (m1 m2 : ('a, 'b) fmap) X:
  eq_except m1 m2 X =>
  eq_except m1.[a <- b] m2.[a <- b] X.
proof.
  rewrite !eq_exceptP=> h x x_notin_X.
  rewrite !getP; case (x = a)=> //=.
  by rewrite h.
qed.

lemma filter_eq_except (m : ('a, 'b) fmap) (X : 'a -> bool):
  eq_except (filter (fun x y => !X x) m) m X.
proof. by rewrite eq_exceptE filter_filter. qed.

lemma eq_except_rem (m1 m2:('a,'b)fmap) (s:'a -> bool) x:
   s x => eq_except m1 m2 s => eq_except m1 (rem x m2) s.
proof.
  rewrite !eq_exceptE rem_filter -filter_predI=> Hmem ->;apply filter_eq=>/#.
qed.

lemma set_eq_except x b (m : ('a, 'b) fmap):
  eq_except m.[x <- b] m (pred1 x).
proof. by rewrite eq_exceptP=> x'; rewrite !getP=> ->. qed.

lemma set2_eq_except x b b' (m : ('a, 'b) fmap):
  eq_except m.[x <- b] m.[x <- b'] (pred1 x).
proof. by rewrite eq_exceptP=> x'; rewrite !getP=> ->. qed.

lemma eq_except_set_eq (m1 m2 : ('a, 'b) fmap) x:
  mem (dom m1) x =>
  eq_except m1 m2 (pred1 x) =>
  m1 = m2.[x <- oget m1.[x]].
proof.
  rewrite eq_exceptP fmapP=> x_in_m1 eqe x'.
  rewrite !getP /oget; case (x' = x)=> [->> |].
    by move: x_in_m1; rewrite in_dom; case (m1.[x]).
  by exact/eqe.
qed.

(* -------------------------------------------------------------------- *)
lemma rem_id (x : 'a) (m : ('a,'b) fmap):
  !mem (dom m) x => rem x m = m.
proof.
rewrite in_dom /= => x_notin_m; apply/fmapP=> x'; rewrite remP.
by case: (x' = x)=> //= ->>; rewrite x_notin_m.
qed.

lemma dom_rem_le (x : 'a) (m : ('a,'b) fmap) (x' : 'a):
  mem (dom (rem x m)) x' => mem (dom m) x'.
proof. by rewrite dom_rem in_fsetD. qed.

lemma rng_rem_le (x : 'a) (m : ('a,'b) fmap) (x' : 'b):
  mem (rng (rem x m)) x' => mem (rng m) x'.
proof. by rewrite rng_rem in_rng=> -[x0] [_ h]; exists x0. qed.

(* -------------------------------------------------------------------- *)
(** FIXME: these two were minimally imported from old and need cleaning *)
lemma leq_card_rng_dom (m:('a,'b) fmap):
  card (rng m) <= card (dom m).
proof.
elim/fset_ind: (dom m) {-2}m (eq_refl (dom m))=> {m} [m /dom_eq0 ->|].
+ by rewrite rng0 dom0 !fcards0.
move=> x s x_notin_s ih m dom_m.
have ->: m = (rem x m).[x <- oget m.[x]].
+ apply fmapP=> x'; rewrite getP remP; case: (x' = x)=> [->|//].
  have /fsetP /(_ x):= dom_m; rewrite in_fsetU in_fset1 /= in_dom.
  by case: m.[x].
have ->:= rng_set (rem x m) x (oget m.[x]).
rewrite fcardU rem_rem fsetI1 fun_if !fcard1 fcards0.
rewrite dom_set fcardUI_indep 2:fcard1.
+ by apply/fsetP=> x0; rewrite in_fsetI dom_rem !inE -andbA andNb.
rewrite StdOrder.IntOrder.ler_subl_addr; apply/StdOrder.IntOrder.ler_paddr.
+ by case: (mem (rng _) _).
apply/StdOrder.IntOrder.ler_add2r/ih/fsetP=> x0.
by rewrite dom_rem dom_m !inE; case: (x0 = x).
qed.

lemma endo_dom_rng (m:('a,'a) fmap):
  (exists x, !mem (dom m) x) =>
  exists x, !mem (rng m) x.
proof.
elim=> x x_notin_m.
have h: 0 < card (((dom m) `|` fset1 x) `\` (rng m)); last first.
+ by have: forall (X : 'a fset), 0 < card X => exists x, mem X x; smt.
rewrite fcardD fcardUI_indep.
+ by apply/fsetP=> x'; rewrite !inE /#.
rewrite fcard1 fsetIUl fcardUI_indep.
+ by apply/fsetP=> x'; rewrite !inE /#.
have ->: card (fset1 x `&` rng m) = if mem (rng m) x then 1 else 0.
+ smt (@FSet).
smt (leq_card_rng_dom @FSet).
qed.

(** TODO: lots of lemmas *)
lemma rem0 (a : 'a) : rem a map0<:'a,'b> = map0.
proof.
  by apply map0_eq0=>x;rewrite remP;case (x=a)=>//=;rewrite map0P.
qed.

lemma set_eq (m:('a,'b)fmap) x y: m.[x] = Some y => m.[x<-y] = m.
proof.
  by rewrite fmapP=> Hx x';rewrite getP;case (x'=x)=>//->;rewrite Hx.
qed.

lemma map_map0 (f:'a -> 'b -> 'c): map f map0 = map0.
proof. by rewrite fmapP=> x;rewrite mapP !map0P. qed.

lemma map_set (f:'a -> 'b -> 'c) m x y :
  map f m.[x<-y] = (map f m).[x<- f x y].
proof.
  by rewrite fmapP=>z;rewrite mapP !getP;case (z=x)=>// _;rewrite mapP.
qed.

lemma map_rem (f:'a -> 'b -> 'c) m x: map f (rem x m) = rem x (map f m).
proof. by rewrite fmapP=>z;rewrite !(mapP,remP)/#. qed.

lemma rem_set (m:('a,'b)fmap) x y v:
  rem x (m.[y<-v]) = if x = y then rem x m else (rem x m).[y<-v].
proof.
  rewrite fmapP=>z;case (x=y)=>[->|]; rewrite !(remP,getP) /#.
qed.

lemma map_comp (f1:'a->'b->'c) (f2:'a->'c->'d) (m:('a,'b)fmap):
   map f2 (map f1 m) = map (fun a b => f2 a (f1 a b)) m.
proof. by rewrite fmapP=>x;rewrite !mapP;case (m.[x]). qed.

lemma map_id (m:('a,'b)fmap): map (fun _ b => b) m = m.
proof. by rewrite fmapP=>x;rewrite mapP;case (m.[x]). qed.
