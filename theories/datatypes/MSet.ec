require import FMap FSet SmtMap Finite List Core AllCore.
require StdBigop.

(* Tactics wishlist *)
lemma eq_imp (y: 'a) x: x = y => x = y by done.

(* Number wishlist *)
lemma maxrA (x y z: int): max (max x y) z = max x (max y z) by smt().

lemma minrA (x y z: int): min (min x y) z = min x (min y z) by smt().

(* List wishlist *)
lemma size1_undup (l: 'a list): size l = 1 => undup l = l.
proof. do 2! (elim l => // ? l _); smt(size_ge0). qed.

lemma count_nseq (x: 'a) n p: count p (nseq n x) = if p x then max 0 n else 0.
proof.
move: n; apply natind => n n_bound /=.
- rewrite nseq0_le //= /#. 
move => IH; rewrite nseqS //= lez_maxr /#.
qed.

lemma nseq_eq (x y: 'a) n m: 
  nseq n x = nseq m y => (x = y /\ n = m) \/ (n <= 0 /\ m <= 0).
proof. smt(size_nseq nth_nseq). qed.

lemma nseq_eq_iff (x y: 'a) n m: 
  nseq n x = nseq m y <=> (x = y /\ n = m) \/ (n <= 0 /\ m <= 0).
proof. smt(nseq_eq nseq0_le). qed.

lemma rem_out (x: 'a) s: !x \in s => rem x s = s.
proof. elim s => // y l /#. qed.

(* FSet wishlist *)
lemma finite_mem (s: 'a fset): is_finite (mem s).
proof. apply mkfinite; exists (elems s) => /#. qed.

lemma subsetU (s1 s2: 'a fset): s1 \subset s2 => s1 `|` s2 = s2.
proof. move => subset. rewrite fsetP => a. rewrite in_fsetU /#. qed.

(* FMap wishlist *) 
op ofset (s: 'a fset): ('a, unit) fmap = 
  ofmap (offun (fun e => if e \in s then Some () else None)).

lemma mem_ofset (s: 'a fset) x: x \in (ofset s) <=> x \in s.
proof.
rewrite /dom getE /ofset ofmapK.
- move: (finite_mem s).
  apply/eq_ind/fun_ext => y.
  rewrite offunE /#.
rewrite offunE /#.
qed.

lemma ofset_get s (e: 'a): (ofset s).[e] = if e \in s then Some () else None.
proof.
rewrite getE /ofset ofmapK.
- move: (finite_mem s).
  apply/eq_ind/fun_ext => y.
  rewrite offunE /#.
rewrite offunE /#.
qed.

lemma ofsetK: cancel ofset fdom<:'a, unit>.
proof. move => s; rewrite fsetP => x; by rewrite mem_fdom mem_ofset. qed.

lemma ofset_mem s (e: 'a): e \in ofset s <=> e \in s.
proof. by rewrite -{2}ofsetK mem_fdom. qed.

op ofsetmap (f: 'a -> 'b) (s: 'a fset) : ('a, 'b) fmap = 
  map (fun x y => f x) (ofset s).

lemma ofsetmapT s (f: 'a -> 'b) e: e \in s => (ofsetmap f s).[e] = Some (f e).
proof. by move => e_in; rewrite /ofsetmap mapE ofset_get e_in. qed.

lemma ofsetmapN s (f: 'a -> 'b) e: e \notin s => (ofsetmap f s).[e] = None.
proof. by move => e_in; rewrite /ofsetmap mapE ofset_get e_in. qed.

lemma mem_ofsetmap s (f: 'a -> 'b) e: e \in ofsetmap f s <=> e \in s.
proof. by rewrite /ofsetmap mem_map ofset_mem. qed.

lemma fsize_ge0 (m: ('a, 'b) fmap): 0 <= fsize m.
proof. by rewrite /fsize fcard_ge0. qed.

lemma rem_set (m: ('a, 'b) fmap) x: x \in m => m = (rem m x).[x <- oget m.[x]].
proof.
move => x_in; apply fmap_eqP => y.
rewrite get_setE remE.
case (y = x) => /#.
qed.

lemma fsize0_empty (m: ('a, 'b) fmap): fsize m = 0 => m = empty.
proof.
move => H.
apply fmap_eqP => x; rewrite emptyE.
case (x \in m) => // x_in. 
apply falseW. 
have /=:= fsize_set (rem m x) x (oget m.[x]).
rewrite -rem_set // H.
have /= ->:= FMap.mem_rem m x x.
smt(fsize_ge0).
qed.

lemma fsize_map m (f: 'a -> 'b -> 'c): fsize (map f m) = fsize m.
proof. by rewrite /fsize fdom_map. qed.

lemma map_eq_empty m (f: 'a ->'b -> 'c): map f m = empty => m = empty.
proof. by move => H; apply fsize0_empty; rewrite -(fsize_map m f) H fsize_empty. qed.

(* -------------------------------------------------------------------- *)
require import Core Int List StdRing StdOrder FMap.
(*---*) import IntOrder.

(* -------------------------------------------------------------------- *)
(* Finite multisets are represented as lists up to permutation          *)

type 'a mset.

op elems  : 'a mset -> 'a list.
op oflist : 'a list -> 'a mset.

axiom elemsK: cancel elems<:'a> oflist.
axiom oflistK (s : 'a list): perm_eq s (elems (oflist s)).

axiom mset_eq (s1 s2 : 'a mset):
  (perm_eq (elems s1) (elems s2)) => (s1 = s2).

(* -------------------------------------------------------------------- *)

lemma perm_eq_oflistP (s1 s2 : 'a list) :
  oflist s1 = oflist s2 <=> perm_eq s1 s2.
proof.
split. 
- move=> oflist_eq; rewrite (perm_eq_trans _ _ _ (oflistK s1)) oflist_eq.
  by rewrite perm_eq_sym oflistK.
move=> peq_s1s2; apply/mset_eq.
apply (perm_eq_trans s1 _ _); 1: rewrite perm_eq_sym oflistK.
rewrite (perm_eq_trans s2 _ _ peq_s1s2) oflistK.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] mult ['a]  (x: 'a) (s: 'a mset): int = count (pred1 x) (elems s).

abbrev "_.[_]" (s: 'a mset) (x: 'a) = mult x s.

lemma count_elems (s : 'a mset):
  forall x, count (pred1 x) (elems s) = s.[x] by rewrite/mult.

lemma mult_oflist (s : 'a list):
  forall x, (oflist s).[x] = count (pred1 x) s.
proof. move => x; rewrite/mult; apply/perm_eqP/perm_eq_sym/oflistK. qed.

lemma mult_ge0 s (x: 'a): 0 <= s.[x] by rewrite/mult; apply count_ge0.

hint exact : mult_ge0.

lemma mset_eqP (s1 s2 : 'a mset):
  (s1 = s2) <=> (forall x, s1.[x] = s2.[x]).
proof.
split=> // h; apply/mset_eq.
rewrite/mult in h.
by rewrite perm_eqP_pred1.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] mem ['a] (s : 'a mset) (x : 'a) = mem (elems s) x.
lemma memE (s : 's mset) x: mem s x = mem (elems s) x by rewrite /mem.

abbrev (\in)    (z : 'a) (s : 'a mset) =  mem s z.
abbrev (\notin) (z : 'a) (s : 'a mset) = !mem s z.

lemma mult_in_ge1 s (x: 'a): x \in s <=> 1 <= mult x s. 
proof. rewrite /mult; have := mem_count x (elems s); rewrite -memE /#. qed.

lemma mult0 s (x: 'a): x \notin s <=> mult x s = 0 by smt(mult_ge0 mult_in_ge1).

lemma mem_oflist (s : 'a list):
  forall x, mem (oflist s) x <=> mem s x.
proof.
move=> x; rewrite !memE (perm_eq_mem _ s) //.
by rewrite perm_eq_sym oflistK.
qed.

(* -------------------------------------------------------------------- *)

op selems (s: 'a mset): 'a fset = oflist (elems s).

lemma mem_selems s (e: 'a): e \in selems s <=> e \in s.
proof. by rewrite /selems mem_oflist memE. qed.

(* -------------------------------------------------------------------- *)

op tofmap (s: 'a mset): ('a, int) fmap = ofsetmap (fun e => s.[e]) (selems s).

lemma tofmap_get (s: 'a mset) e: (tofmap s).[e] = if e \in s then Some(s.[e]) else None.
proof.
rewrite /tofmap.
case (e \in s) => e_in.
- by rewrite ofsetmapT 1:mem_selems.
by rewrite ofsetmapN 1:mem_selems.
qed.

op offmap (m: ('a, int) fmap): 'a mset = 
  oflist (flatten (FSet.elems (FMap.frng (FMap.map (fun (a: 'a) (n: int) => nseq n a) m)))).

lemma mem_tofmap (s: 'a mset) e: e \in tofmap s <=> e \in s.
proof. by rewrite /tofmap /= mem_ofsetmap mem_selems. qed.

lemma offmap_mult (m: ('a, int) fmap) e: (offmap m).[e] = 
  max 0 (odflt 0 m.[e]).
proof.
rewrite /offmap mult_oflist count_flatten StdBigop.Bigint.sumzE.
rewrite StdBigop.Bigint.BIA.big_mapT /(\o).
pose l:= (frng (map (fun (a : 'a) (n : int) => nseq n a) m)).
have lP: forall il, il \in l <=> exists a, a \in m /\ il = nseq (oget m.[a]) a.
- rewrite /l => il; rewrite mem_frng /rng. 
  apply exists_iff => x /=.
  rewrite mapE /=.
  pose opt_n:= m.[x].
  have: opt_n = m.[x] by done.
  rewrite /dom.
  case (opt_n) => [/= /eq_sym -> //|n <- //=].
move: m l lP; apply fmapW => /= [l lP|m k v k_in IH l lP].
- have ->: l = fset0.
  + apply in_eq_fset0 => il.
    rewrite -negP => /lP [k].
    by rewrite mem_empty.
  rewrite emptyE /= maxrE /= elems_fset0 /=.
  exact StdBigop.Bigint.BIA.big_nil.
rewrite mem_fdom /dom /= in k_in.
case (exists a, a \in m /\ nseq (oget m.[a]) a = nseq v k) => 
  [[x [x_in eq_nseq]]| /negb_exists /= neq_nseq].
- have := IH l => IH'; clear IH.
  have := nseq_eq _ _ _ _ eq_nseq.
  have x_neq : x <> k.
  + rewrite -negP => x_eq; subst x.
    by rewrite /dom k_in in x_in.
  rewrite x_neq /= => [[mx_le0 v_le0]].
  rewrite IH' => [il|]; first last. 
  + case (e = k) => e_eq; 2: by rewrite get_set_neqE.    
    subst e; rewrite get_set_sameE k_in /= lez_maxl // lez_maxl //.
  rewrite lP.
  split => [[a [/mem_set [a_in|->] ->]]|[a [a_in ->]]].
  + by exists a; rewrite a_in /= get_set_neqE 1:/#. 
  + by exists x; rewrite x_in /= get_set_sameE eq_nseq.
  have a_neq: a <> k.
  + rewrite -negP => a_eq; subst a.
    by rewrite /dom k_in in a_in.
  by exists a; rewrite get_set_neqE // mem_set a_in.
have nseq_in: nseq v k \in l by rewrite lP; exists k; rewrite get_set_sameE mem_set.
have perm:= FSet.perm_to_rem _ _ nseq_in.
rewrite (StdBigop.Bigint.BIA.eq_big_perm _ _ _ _ perm) StdBigop.Bigint.BIA.big_consT.
rewrite count_nseq {1}/pred1.
case (k = e) => /= e_eq; 1:subst e.
- rewrite get_set_sameE /=.
  rewrite StdBigop.Bigint.BIA.big1_seq; 2:by exact addz0.
  rewrite /predT => il /=.
  rewrite -memE in_fsetD1 => [[/lP [x [/mem_set [x_in|->] ->]]]]; 
    rewrite count_nseq {1}/pred1 /=.
  + by have -> /=: x <> k by rewrite -negP => x_eq; subst x; rewrite /dom k_in in x_in.
  by rewrite get_set_sameE /=.    
rewrite get_set_neqE eq_sym // IH // => il.
rewrite in_fsetD lP exists_andr.
apply exists_iff => x /=.
rewrite mem_set in_fset1.
case (x = k) => [-> /=| /= x_neq].
* by rewrite /dom k_in get_set_sameE /= andbN.
rewrite get_set_neqE //.
split => [->//|[x_in ->]].
rewrite x_in /=.
have := neq_nseq x.
by rewrite x_in.
qed.

lemma tofmapK: cancel tofmap<:'a> offmap.
proof. 
move => s; apply mset_eqP => y.
rewrite offmap_mult tofmap_get.
case (y \in s) => y_in; rewrite lez_maxr //.
by rewrite eq_sym; apply mult0.
qed.

lemma offmapK (x: ('a, int) fmap): 
  (forall e, e \in x => 1 <= oget x.[e]) => tofmap (offmap x) = x.
proof.
move => H; apply fmap_eqP => e.
rewrite tofmap_get mult_in_ge1 offmap_mult.
case (e \in x) => [/H /#|].
rewrite /dom /= => -> /=.
by rewrite lez_maxr.
qed.
(* don't like this part of the API
lemma tofmap_range (x: ('a, int) fmap):
  (forall y, y \in x => 1 <= oget x.[y]) <=> exists (y : 'a mset), x = tofmap y.
proof.
split => [mult_pos|[s -> e e_in]].
- by exists (offmap x); rewrite eq_sym; apply offmapK.
rewrite mem_tofmap in e_in.
rewrite tofmap_get e_in /=.
by apply mult_in_ge1.
qed.

lemma tofmap_inj: injective tofmap<:'a> by apply/(can_inj _ offmap)/tofmapK.

lemma tofmapP s: (forall y, y \in (tofmap<:'a> s) => 1 <= oget (tofmap s).[y]).
proof. by rewrite tofmap_range; exists s. qed.
*)

(* -------------------------------------------------------------------- *)
op [opaque] mset0 ['a] = oflist [<:'a>].

lemma mset0_mult (e: 'a): mset0.[e] = 0.
proof. by rewrite /mset0 mult_oflist. qed.

op [opaque] mset1 ['a] (z : 'a) = oflist [z].

lemma mset1_mult (x y: 'a): (mset1 x).[y] = b2i (x = y).
proof. by rewrite /mset1 mult_oflist /= /pred1. qed.

op [opaque] add ['a] (s1 s2 : 'a mset) = offmap (merge 
  (fun a m n, if is_some m \/ is_some n then Some (odflt 0 m + odflt 0 n) else None) 
  (tofmap s1) (tofmap s2)).

abbrev (+) ['a] = add<:'a>.

lemma add_mult (s1 s2: 'a mset) e: (s1 + s2).[e] = s1.[e] + s2.[e].
proof. rewrite /add offmap_mult mergeE //= !tofmap_get; smt(mult_ge0 mult0). qed.

op [opaque] union ['a] (s1 s2 : 'a mset) = offmap (merge 
  (fun a m n, if is_some m \/ is_some n then Some (max (odflt 0 m) (odflt 0 n)) else None) 
  (tofmap s1) (tofmap s2)).

abbrev (`|`) ['a] = union<:'a>.

lemma union_mult (s1 s2: 'a mset) e: (s1 `|` s2).[e] = max s1.[e] s2.[e].
proof. rewrite /union offmap_mult mergeE //= !tofmap_get; smt(mult_ge0 mult0). qed.

op [opaque] intersection ['a] (s1 s2 : 'a mset) = offmap (merge 
  (fun a m n, if is_some m /\ is_some n then Some (min (odflt 0 m) (odflt 0 n)) else None) 
  (tofmap s1) (tofmap s2)).

abbrev (`&`) ['a] = intersection<:'a>.

lemma intersection_mult (s1 s2: 'a mset) e: (s1 `&` s2).[e] = min s1.[e] s2.[e].
proof. rewrite /intersection offmap_mult mergeE //= !tofmap_get; smt(mult_ge0 mult0). qed.

op [opaque] diff ['a] (s1 s2 : 'a mset) = offmap (merge 
  (fun a m n, if is_some m then Some (odflt 0 m - odflt 0 n) else None) 
  (tofmap s1) (tofmap s2)).

abbrev (`\`) ['a] = diff<:'a>.

lemma diff_mult (s1 s2: 'a mset) e: (s1 `\` s2).[e] = max 0 (s1.[e] - s2.[e]).
proof. rewrite /diff offmap_mult mergeE //= !tofmap_get; smt(mult_ge0 mult0). qed.

op rem ['a] (s : 'a mset) x = s `\` mset1 x.

lemma rem_mult s (x y: 'a): (rem s x).[y] = max 0 (s.[y] - b2i (x = y)).
proof. by rewrite diff_mult mset1_mult. qed.

op insert ['a] (s : 'a mset) x = s + mset1 x.

lemma insert_mult s (x y: 'a): (insert s x).[y] = s.[y] + b2i (x = y).
proof. by rewrite add_mult mset1_mult. qed.

(* -------------------------------------------------------------------- *)
(*
lemma in_mset0 (x: 'a): x \in mset0 <=> false.
proof. by rewrite /mset0 mem_oflist. qed.

lemma in_eq_mset0 ['a] (X : 'a mset): (forall x, !x \in X) => X = mset0.
proof. by move=> mem_X; apply/msetP=> x; rewrite mset0P -mult0 mem_X. qed.
*)
lemma elems_mset0 ['a]: elems mset0 = [<:'a>].
proof. 
rewrite /mset0; apply/perm_eq_small/perm_eq_sym => //=.
rewrite -{1}(undup_id []) // oflistK //.
qed.
(*
lemma elems_eq_mset0 ['a] (A : 'a mset): elems A = [<:'a>] => A = mset0.
proof.
move=> elems_nil; apply/msetP=> x. rewrite mset0P.
by rewrite -mult0 /mem elems_nil.
qed.

lemma in_mset1 z: forall x, mem (mset1<:'a> z) x <=> x = z.
proof. by rewrite /mset1 /= => x; rewrite mem_oflist. qed.

(*
lemma in_eq_mset1 ['a] (X : 'a mset) x0:
  (forall x, x \in X <=> x = x0) => X = mset1 x0.
proof. by move=> mem_X; apply/msetP=> x; rewrite in_mset1 mem_X. qed.
*)
*)
lemma elems_mset1 (x : 'a) : elems (mset1 x) = [x].
proof.
rewrite /mset1; apply/perm_eq_small/perm_eq_sym=> //=.
by rewrite -{1}(undup_id [x]) ?oflistK.
qed.
(*
lemma elems_eq_mset1 (A : 'a mset) x : elems A = [x] => A = mset1 x.
proof.
by move=> elems_x; apply/msetP=> x0; rewrite /mult elems_mset1 elems_x.
qed.

lemma in_msetU (s1 s2 : 'a mset):
  forall x, x \in (s1 `|` s2) <=> x \in s1 \/ x \in s2.
proof. move => x; rewrite !mult_in_ge1 unionP; smt(mult_ge0). qed.

lemma in_msetI (s1 s2 : 'a mset):
  forall x, x \in (s1 `&` s2) <=> x \in s1 /\ x \in s2.
proof. move => x. rewrite !mult_in_ge1 intersectionP /#. qed.

lemma in_msetD (s1 s2 : 'a mset):
  forall x, x \in (s1 `\` s2) <=> s2.[x] < s1.[x].
proof. move => x; rewrite mult_in_ge1 remP /#. qed.

lemma msetD1E (s : 'a mset) x :
  perm_eq (elems (s `\` mset1 x)) (rem x (elems s)).
proof. 
apply perm_eqP_pred1 => e.
rewrite -/(mult e (s `\`mset1 x)) remP mset1P.
apply (addzI (b2i (pred1 e x))).
case (x \in s) => x_in.
- rewrite -(count_rem (pred1 e)) -?memE // -/(mult e s) /pred1.
  smt(mult_in_ge1 mult_ge0).
rewrite rem_out 1:-memE // -/(mult e s) /pred1 /b2i.
case (x = e) => /=; 1:smt(mult0).
smt(mult_ge0).
qed.

lemma perm_to_rem (s:'a mset) x :
  mem s x => perm_eq (elems s) (x :: elems (s `\` mset1 x)).
proof.
rewrite memE => /perm_to_rem /perm_eqlP->; apply/perm_cons.
have /perm_eqlP <- := (msetD1E s x); rewrite perm_eq_refl.
qed.

(* -------------------------------------------------------------------- *)

*)
hint rewrite multE : mset0_mult mset1_mult add_mult union_mult  
  intersection_mult diff_mult.

lemma oflist_cons ['a] (x : 'a) s : oflist (x::s) = insert (oflist s) x.
proof. 
apply mset_eqP => z.
rewrite mult_oflist /= !multE /mult {1}/pred1 addzC.
congr; apply perm_eqP_pred1.
exact oflistK.
qed.
(*
lemma oflist_cat ['a] (s1 s2 : 'a list) : 
  oflist (s1 ++ s2) = oflist s1 `|` oflist s2.
proof. by apply fsetP => z; rewrite in_fsetU !mem_oflist mem_cat. qed.

(* -------------------------------------------------------------------- *)
lemma in_fsetU1 (s : 'a fset) x:
  forall x', mem (s `|` fset1 x) x' <=> mem s x' \/ x' = x.
proof. by move=> x'; rewrite in_fsetU in_fset1. qed.

lemma in_fsetI1 (s : 'a fset) x:
  forall x', mem (s `&` fset1 x) x' <=> mem s x /\ x' = x.
proof. by move=> x'; rewrite in_fsetI in_fset1. qed.

lemma in_fsetD1 (s : 'a fset) x:
  forall x', mem (s `\` fset1 x) x' <=> mem s x' /\ x' <> x.
proof. by move=> x'; rewrite in_fsetD in_fset1. qed.
*)
(* -------------------------------------------------------------------- *)
abbrev disjoint (xs ys : 'a mset) = xs `&` ys = mset0.

lemma disjointP (xs ys : 'a mset):
  disjoint xs ys <=> forall (x : 'a), x \in xs => ! x \in ys.
proof.
split=> [disj_xs_ys x /mult_in_ge1 x_in_xs | all_xs_not_in_ys].
- have := mset_eqP (xs `&` ys) mset0.
  rewrite mult_in_ge1 {1}disj_xs_ys /= => inI_eq0 {disj_xs_ys}.
  have:= inI_eq0 x; clear inI_eq0.  
  rewrite !multE /#.
rewrite mset_eqP => x.
have := all_xs_not_in_ys x.
rewrite !multE !mult_in_ge1.
smt(mult_ge0).
qed.

(* -------------------------------------------------------------------- *)
op [opaque] pick ['a] (A : 'a fset) = head witness (elems A).
lemma pickE (A : 'a fset): pick A = head witness (elems A) by rewrite/pick.

lemma pick0: pick<:'a> fset0 = witness.
proof. by rewrite pickE elems_fset0. qed.

lemma mem_pick (A : 'a fset): A <> fset0 => mem A (pick A).
proof.
move=> /(contra _ _ (elems_eq_fset0 A)); rewrite pickE memE.
by move=> /(mem_head_behead witness) <-.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] filter ['a] (p : 'a -> bool) (s : 'a fset) =
  oflist (filter p (elems s)).
lemma filterE (p: 'a -> bool) s: filter p s = oflist (filter p (elems s)).
proof. by rewrite/filter. qed.

(* -------------------------------------------------------------------- *)
lemma in_filter (p : 'a -> bool) (s : 'a fset):
  forall x, mem (filter p s) x <=> p x /\ mem s x.
proof. by move=> x; rewrite filterE mem_oflist mem_filter memE. qed.

lemma filter0 (p : 'a -> bool): filter p fset0 = fset0.
proof. by apply/fsetP=> x; rewrite in_filter in_fset0. qed.

lemma filter1 (p : 'a -> bool) (a : 'a):
  filter p (fset1 a) = if (p a) then fset1 a else fset0.
proof.
apply/fsetP=> x; rewrite in_filter fun_if2 in_fset1 in_fset0.
by case (x = a).
qed.

lemma filterU (p : 'a -> bool) (A B : 'a fset):
  filter p (A `|` B) = filter p A `|` filter p B.
proof. by apply/fsetP=> x; rewrite !(inE,in_filter) andb_orr. qed.

lemma filterI (p : 'a -> bool) (A B : 'a fset):
  filter p (A `&` B) = filter p A `&` filter p B.
proof. by apply/fsetP=> x; rewrite !(inE,in_filter) andbACA andbb. qed.

lemma filterD (p : 'a -> bool) (A B : 'a fset):
  filter p (A `\` B) = filter p A `\` filter p B.
proof.
apply/fsetP=> x; rewrite !(inE,in_filter) !negb_and andb_orr.
by rewrite andbAC andbN andbA.
qed.

lemma filter_pred0 (A : 'a fset): filter pred0 A = fset0.
proof. by apply/fsetP=> x; rewrite in_fset0 in_filter. qed.

lemma filter_pred1 (a : 'a) (A : 'a fset):
  filter (pred1 a) A = if mem A a then fset1 a else fset0.
proof.
apply/fsetP=> x; rewrite in_filter fun_if2 !inE.
by case (x = a)=> @/pred1 ->.
qed.

lemma filter_mem (A B : 'a fset): filter (mem A) B = A `&` B.
proof. by apply/fsetP=> x; rewrite in_fsetI in_filter. qed.

lemma filter_memC (A B : 'a fset): filter (predC (mem A)) B = B `\` A.
proof. by apply/fsetP=> x; rewrite in_fsetD in_filter andbC. qed.
*)
(* -------------------------------------------------------------------- *)
op (\subset) (s1 s2 : 'a mset) = forall x, s1 .[x] <= s2.[x].
op (\proper) (s1 s2 : 'a mset) = s1 \subset s2 /\ s1 <> s2.

lemma diff_mult_subset (s1 s2 : 'a mset): s2 \subset s1 => 
  forall x, (s1 `\` s2).[x] = s1.[x] - s2.[x].
proof. move => s1_sub_s2 x; rewrite diff_mult => /#. qed.
(*
lemma subsetP (s1 s2 : 'a fset):
  (s1 \subset s2) <=> (mem s1 <= mem s2).
proof. by []. qed.
*)
lemma subset_trans (s1 s2 s3 : 'a mset): 
  s1 \subset s2 => s2 \subset s3 => s1 \subset s3.
proof. move=> le1 le2 x; exact (lez_trans _ _ _ (le1 x) (le2 x)). qed.

lemma properP (s1 s2 : 'a mset) :
  s1 \proper s2 <=> s1 \subset s2 /\ exists x, s1.[x] < s2.[x].
proof.
rewrite /(\proper) &(andb_id2l) mset_eqP negb_forall /= => le_XY.
apply/eqboolP/exists_eq => x /= /#.
qed.

(* -------------------------------------------------------------------- *)
lemma eqEsubset (s1 s2 : 'a mset) : 
  (s1 = s2) <=> (s1 \subset s2) /\ (s2 \subset s1).
proof. rewrite mset_eqP => /#. qed.

(* -------------------------------------------------------------------- *)
lemma mset_ind (p : 'a mset -> bool):
  p mset0 =>
  (forall x s, p s => p (insert s x)) =>
  (forall s, p s).
proof.
move=> p0 pa s; rewrite -elemsK.
elim (elems s)=> {s} [|x s ih].
- by rewrite -/mset0.
rewrite oflist_cons.
by apply pa.
qed.

(* ------------------------------------------------------------------ *)
lemma addsC (A B : 'a mset) : A + B = B + A.
proof. by apply/mset_eqP => x; rewrite !multE addzC. qed.

lemma add0s (A : 'a mset) : mset0 + A = A.
proof. by apply/mset_eqP => x; rewrite !multE. qed.

lemma adds0 (A : 'a mset) : A + mset0 = A.
proof. by apply/mset_eqP => x; rewrite !multE. qed.

lemma addsA (A B C : 'a mset) : A + (B + C) = A + B + C.
proof. by apply/mset_eqP => x; rewrite !multE addzA. qed.

lemma addsCA (A B C : 'a mset) : A + (B + C) = B + (A + C).
proof. by rewrite !addsA (addsC B). qed.

lemma addsAC (A B C : 'a mset) : A + B + C = A + C + B.
proof. by rewrite -!addsA (addsC B). qed.

lemma addsUACA (A B C D : 'a mset) : (A + B) + (C + D) = (A + C) + (B + D).
proof. by rewrite -!addsA (addsCA B). qed.

(* ------------------------------------------------------------------ *)
lemma msetUC (A B : 'a mset) : A `|` B = B `|` A.
proof. by apply/mset_eqP => x; rewrite !multE maxrC. qed.

lemma mset0U (A : 'a mset) : mset0 `|` A = A.
proof. by apply/mset_eqP => x; rewrite !multE; smt(mult_ge0). qed.

lemma msetU0 (A : 'a mset) : A `|` mset0 = A.
proof. by apply/mset_eqP => x; rewrite !multE; smt(mult_ge0). qed.

lemma msetUA (A B C : 'a mset) : A `|` (B `|` C) = A `|` B `|` C.
proof. by apply/mset_eqP => x; rewrite !multE maxrA. qed.

lemma msetUCA (A B C : 'a mset) : A `|` (B `|` C) = B `|` (A `|` C).
proof. by rewrite !msetUA (msetUC B). qed.

lemma msetUAC (A B C : 'a mset) : A `|` B `|` C = A `|` C `|` B.
proof. by rewrite -!msetUA (msetUC B). qed.

lemma msetUACA (A B C D : 'a mset) : (A `|` B) `|` (C `|` D) = (A `|` C) `|` (B `|` D).
proof. by rewrite -!msetUA (msetUCA B). qed.

lemma msetUid (A : 'a mset) : A `|` A = A.
proof. by apply/mset_eqP=> x; rewrite !multE. qed.

lemma msetUUl (A B C : 'a mset) : A `|` B `|` C = (A `|` C) `|` (B `|` C).
proof. by rewrite msetUA (msetUAC _ C) -(msetUA _ C) msetUid. qed.

lemma msetUUr (A B C : 'a mset) : A `|` (B `|` C) = (A `|` B) `|` (A `|` C).
proof. by rewrite !(msetUC A) msetUUl. qed.

(* ------------------------------------------------------------------ *)
lemma msetIC (A B : 'a mset) : A `&` B = B `&` A.
proof. by apply/mset_eqP => x; rewrite !multE minrC. qed.

lemma mset0I (A : 'a mset) : mset0 `&` A = mset0.
proof. by apply/mset_eqP => x; rewrite !multE lez_minl. qed.

lemma msetI0 (A : 'a mset) : A `&` mset0 = mset0.
proof. by rewrite msetIC mset0I. qed.

lemma mset1I (x : 'a) (D : 'a mset):
  mset1 x `&` D = if x \in D then mset1 x else mset0.
proof.
apply/mset_eqP=> y; rewrite (fun_if2 "_.[_]") /= !multE mult_in_ge1.
smt(mult_ge0).
qed.

lemma msetI1 (x : 'a) (D : 'a mset):
  D `&` mset1 x = if x \in D then mset1 x else mset0.
proof. by rewrite msetIC mset1I. qed.

lemma msetIA (A B C : 'a mset) : A `&` (B `&` C) = A `&` B `&` C.
proof. by apply/mset_eqP=> x; rewrite !multE minrA. qed.

lemma msetICA (A B C : 'a mset) : A `&` (B `&` C) = B `&` (A `&` C).
proof. by rewrite !msetIA (msetIC A). qed.

lemma msetIAC (A B C : 'a mset) : A `&` B `&` C = A `&` C `&` B.
proof. by rewrite -!msetIA (msetIC B). qed.

lemma msetIACA (A B C D : 'a mset) : (A `&` B) `&` (C `&` D) = (A `&` C) `&` (B `&` D).
proof. by rewrite -!msetIA (msetICA B). qed.

lemma msetIid (A : 'a mset) : A `&` A = A.
proof. by apply/mset_eqP=> x; rewrite !multE. qed.

lemma msetIIl (A B C : 'a mset) : A `&` B `&` C = (A `&` C) `&` (B `&` C).
proof. by rewrite msetIA (msetIAC _ C) -(msetIA _ C) msetIid. qed.

lemma msetIIr (A B C : 'a mset) : A `&` (B `&` C) = (A `&` B) `&` (A `&` C).
proof. by rewrite !(msetIC A) msetIIl. qed.

(* ------------------------------------------------------------------ *)
lemma msetIUr (A B C : 'a mset) : A `&` (B `|` C) = (A `&` B) `|` (A `&` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetIUl (A B C : 'a mset) : (A `|` B) `&` C = (A `&` C) `|` (B `&` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetUIr (A B C : 'a mset) : A `|` (B `&` C) = (A `|` B) `&` (A `|` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetUIl (A B C : 'a mset) : (A `&` B) `|` C = (A `|` C) `&` (B `|` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetUK (A B : 'a mset) : (A `|` B) `&` A = A.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetKU (A B : 'a mset) : A `&` (B `|` A) = A.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetIK (A B : 'a mset) : (A `&` B) `|` A = A.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetKI (A B : 'a mset) : A `|` (B `&` A) = A.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetadd_eq_union (A B : 'mset) : A `&` B = mset0 => 

(* ------------------------------------------------------------------ *)
lemma msetD0 (A : 'a mset) : A `\` mset0 = A.
proof. by apply/mset_eqP=> x; rewrite !multE /= ler_maxr. qed.

lemma mset0D (A : 'a mset) : mset0 `\` A = mset0.
proof. apply/mset_eqP=> x; rewrite !multE /=; smt(mult_ge0). qed.

lemma mset1D (x : 'a) (D : 'a mset):
  mset1 x `\` D = if mem D x then mset0 else mset1 x.
proof.
apply/mset_eqP=> y; rewrite (fun_if2 "_.[_]") !multE /= !multE mult_in_ge1.
smt(mult_ge0).
qed.

lemma msetDv (A : 'a mset) : A `\` A = mset0.
proof. by apply/mset_eqP=> x; rewrite !multE. qed.

lemma msetaddD (A B : 'a mset) : (A + B) `\` A = B.
proof. apply mset_eqP => x; rewrite !multE; smt(mult_ge0). qed.

(* not true for multisets 
lemma msetID (A B : 'a mset) : A `&` B `|` A `\` B = A.
proof. apply/mset_eqP=> x; rewrite !multE. -andb_orr orbN andbT. qed.

lemma msetII (A B : 'a mset) : (A `&` B) `&` (A `\` B) = mset0.
proof. apply/mset_eqP=> x; rewrite !multE. andbACA andbN andbF. qed.
*)
lemma msetDUl (A B C : 'a mset) : (A `|` B) `\` C = (A `\` C) `|` (B `\` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetDUr (A B C : 'a mset) : A `\` (B `|` C) = (A `\` B) `&` (A `\` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetDIl (A B C : 'a mset) : (A `&` B) `\` C = (A `\` C) `&` (B `\` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

(* not true for multisets
lemma msetIDA (A B C : 'a mset) : A `&` (B `\` C) = (A `&` B) `\` C.
proof. apply/mset_eqP=> x; rewrite !multE. /#. qed.

lemma msetIDAC (A B C : 'a mset) : (A `\` B) `&` C = (A `&` C) `\` B.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.
*)

lemma msetDIr (A B C : 'a mset) : A `\` (B `&` C) = (A `\` B) `|` (A `\` C).
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetDDl (A B C : 'a mset) : (A `\` B) `\` C = A `\` (B + C).
proof. apply/mset_eqP=> x; rewrite !multE; smt(mult_ge0). qed.

(* not true for multisets
lemma msetDDr (A B C : 'a mset) : A `\` (B `\` C) = (A `\` B) `|` (A `&` C).
proof. apply/mset_eqP=> x; rewrite !multE. smt(mult_ge0). qed.
*)

lemma msetDK (A B : 'a mset) : (A `|` B) `\` B = A `\` B.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

lemma msetDKv (A B : 'a mset) : (A `&` B) `\` B = mset0.
proof. apply/mset_eqP=> x; rewrite !multE /#. qed.

(* -------------------------------------------------------------------- *)
lemma subsetIl (A B : 'a mset) : (A `&` B) \subset A.
proof. rewrite /(\subset) => x; rewrite multE /#. qed.

lemma subsetIr (A B : 'a mset) : (A `&` B) \subset B.
proof. rewrite /(\subset) => x; rewrite multE /#. qed.

(* -------------------------------------------------------------------- *)
lemma subsetDl (A B : 'a mset) : A `\` B \subset A.
proof. rewrite /(\subset) => x; rewrite multE; smt(mult_ge0). qed.

(* -------------------------------------------------------------------- *)
lemma sub0set (A : 'a mset) : mset0 \subset A.
proof. rewrite /(\subset) => x; rewrite multE mult_ge0. qed.

lemma sub1set x (A : 'a mset) : mset1 x \subset A <=> x \in A.
proof.
rewrite mult_in_ge1 /(\subset) -b2i1 (eq_imp (x = x) true) // -(mset1_mult x).
split => [->//|H y].
case (x = y) => [//|].
by rewrite mset1_mult => ->.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] card ['a] (s : 'a mset) = size (elems s). 

lemma mcards0: card mset0<:'a> = 0.
proof. by rewrite /card elems_mset0. qed.

lemma eq_mcards0 (A : 'a mset): A = mset0 => card A = 0.
proof. by move=> ->; apply/mcards0. qed.

lemma mcard_ge0 (A : 'a mset) : 0 <= card A.
proof. by rewrite /card size_ge0. qed.

lemma mcard1 (x : 'a) : card (mset1 x) = 1.
proof. by rewrite /card elems_mset1. qed.

(* -------------------------------------------------------------------- *)
lemma mcardUI_indep (A B : 'a mset) : A `&` B = mset0 =>
  card (A `|` B) = card A + card B.
proof.
move/fsetP=> h; rewrite setUE !cardE; pose s := _ ++ _.
rewrite -(perm_eq_size _ _ (oflistK s)) undup_id /s 2:size_cat //.
rewrite cat_uniq ?uniq_elems /= -implybF => /hasP [x [Bx Ax]].
by have:= h x; rewrite in_fsetI in_fset0 !memE Bx Ax.
qed.

lemma fcardUI (A B : 'a fset) :
  card (A `|` B) + card (A `&` B) = card A + card B.
proof.
rewrite -(fsetID (A `|` B) A) fsetUK (fsetUC A B) fsetDK.
rewrite fcardUI_indep.
+ by rewrite fsetIDA fsetDIl fsetDv fset0I.
by rewrite addzAC fsetIC -addzA -fcardUI_indep ?fsetID ?fsetII.
qed.

(* -------------------------------------------------------------------- *)
lemma fcardU (A B : 'a fset) :
  card (A `|` B) = card A + card B - card (A `&` B).
proof. by rewrite -fcardUI Ring.IntID.addrK. qed.

lemma fcardI (A B : 'a fset) :
  card (A `&` B) = card A + card B - card (A `|` B).
proof. by rewrite -fcardUI addzAC subzz. qed.

(* -------------------------------------------------------------------- *)
lemma fcardID (A B : 'a fset) :
  card (A `&` B) + card (A `\` B) = card A.
proof. by rewrite -fcardUI_indep ?fsetID // fsetII. qed.

lemma fcardD (A B : 'a fset) :
  card (A `\` B) = card A - card (A `&` B).
proof. by rewrite -(fcardID A B) addzAC subzz. qed.

(* -------------------------------------------------------------------- *)

lemma fcardI1 (A : 'a fset) x : 
  card (A `&` fset1 x) = b2i (x \in A).
proof.
by rewrite fsetI1; case: (x \in A) => _; rewrite ?fcard1 ?fcards0.
qed.

lemma fcardU1 (A : 'a fset) x : 
  card (A `|` fset1 x) = b2i (x \notin A) + card A.
proof. by rewrite fcardU fcard1 fcardI1 /#. qed.

lemma fcardD1 (A : 'a fset) (x : 'a) :
  card A = card (A `\` fset1 x) + (if mem A x then 1 else 0).
proof. by rewrite fcardD fcardI1; ring. qed.

(* -------------------------------------------------------------------- *)

lemma fcard_oflist (s : 'a list) : card (oflist s) <= size s.
proof. by rewrite /card -(perm_eq_size _ _ (oflistK s)) size_undup. qed.

lemma uniq_card_oflist (s : 'a list) : uniq s => card (oflist s) = size s.
proof. by rewrite /card => /oflist_uniq/perm_eq_size => <-. qed.

lemma card_iota (n : int) : 0 <= n => card (oflist (iota_ 1 n)) = n.
proof. 
by move=> n_ge0; rewrite uniq_card_oflist ?iota_uniq size_iota /#. 
qed.

(* -------------------------------------------------------------------- *)
lemma subset_fsetU_id (A B : 'a fset) :
  A \subset B => A `|` B = B.
proof.
move=> A_le_B; apply/fsetP=> x; rewrite in_fsetU.
by split=> [[/A_le_B|->]|->].
qed.

lemma subset_fsetI_id (A B : 'a fset) :
  B \subset A => A `&` B = B.
proof.
move=> B_le_A; apply/fsetP=> x; rewrite in_fsetI.
by split=> [[_ ->]|^x_in_B /B_le_A].
qed.

lemma subset_leq_fcard (A B : 'a fset) :
  A \subset B => card A <= card B.
proof.
move=> /subsetP le_AB; rewrite -(fcardID B A).
have ->: B `&` A = A; 1: apply/fsetP=> x.
  by rewrite in_fsetI andb_idl //; apply/le_AB.
by apply/ler_addl; apply/fcard_ge0.
qed.

(* -------------------------------------------------------------------- *)
lemma subset_cardP (A B : 'a fset) :
  card A = card B => (A = B <=> A \subset B).
proof.                          (* FIXME: views *)
  move=> eqcAB; split=> [->// |]; rewrite eqEsubset.
  move=> le_AB; split=> // x Bx; case: (mem A x) => // Ax.
  rewrite -(ltrr (card A)) {2}eqcAB (fcardD1 B x) Bx /=.
  rewrite addzC -lez_add1r ler_add //; apply/subset_leq_fcard.
  apply/subsetP=> y Ay; rewrite !inE le_AB //=; move: Ax.
  by apply/absurd=> /= <-.
qed.

(* -------------------------------------------------------------------- *)
lemma eqEcard (A B : 'a fset) :
  (A = B) <=> (A \subset B) /\ (card B <= card A).
proof.
  split=> [->// |]; case=> le_AB le_cAB; rewrite subset_cardP //.
  by rewrite eqr_le le_cAB /=; apply/subset_leq_fcard.
qed.

(* -------------------------------------------------------------------- *)
lemma fcard_eq0 (A : 'a fset) : (card A = 0) <=> (A = fset0).
proof.
  split=> [z_cA|]; last by move=> ->; apply/fcards0.
  rewrite eq_sym eqEcard z_cA fcards0 //=; apply/sub0set.
qed.

lemma fcard_eq1 (A : 'a fset) : (card A = 1) <=> (exists a, A = fset1 a).
proof.
split=> [o_cA|[a ->]]; last apply/fcard1.
exists (pick A); rewrite eq_sym eqEcard o_cA fcard1 /= sub1set mem_pick.
by apply: contraL o_cA => ->; rewrite fcards0.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] image (f: 'a -> 'b) (A : 'a fset): 'b fset = 
  oflist (map f (elems A)).
lemma imageE (f: 'a -> 'b) A: image f A = oflist (map f (elems A)).
proof. by rewrite/image. qed.

lemma imageP (f : 'a -> 'b) (A : 'a fset) (b : 'b):
  mem (image f A) b <=> (exists a, mem A a /\ f a = b).
proof.
  rewrite imageE mem_oflist mapP; split.
    by move=> [a] [x_in_A ->]; exists a; rewrite memE.
  by move=> [a] [x_in_A <-]; exists a; rewrite -memE.
qed.

lemma mem_image (f:'a->'b) (s:'a fset) x:
  mem s x => mem (image f s) (f x).
proof. by rewrite imageP=> ?;exists x. qed.

lemma image0 (f : 'a -> 'b): image f fset0 = fset0.
proof.
  by apply/fsetP=> b; rewrite imageP; split=> [[a]|]; rewrite in_fset0.
qed.

lemma image1 (f : 'a -> 'b) (a : 'a):
  image f (fset1 a) = fset1 (f a).
proof.
  apply/fsetP=> b; rewrite imageP in_fset1.
  by split=> [[a']|->]; [|exists a]; rewrite in_fset1.
qed.

lemma imageU (f : 'a -> 'b) (A B : 'a fset):
  image f (A `|` B) = image f A `|` image f B.
proof.
  apply/fsetP=> x; rewrite in_fsetU !imageP; split.
    by move=> [x']; rewrite in_fsetU=> -[[x'_in_A|x'_in_B] <-];
       [left|right]; exists x'.
  by move=> [[x'] [x'_in_X] <-|[x'] [x'_in_X] <-];
     exists x'; rewrite in_fsetU x'_in_X.
qed.

lemma imageI (f : 'a -> 'b) (A B : 'a fset):
  image f (A `&` B) \subset image f A `&` image f B.
proof.
  move=> x; rewrite !inE !imageP=> -[a].
  rewrite !inE=> -[[a_in_A a_in_B] <-].
  by split; exists a.
qed.

lemma imageD (f : 'a -> 'b) (A B : 'a fset):
  image f A `\` image f B \subset image f (A `\` B).
proof.
  move=> x; rewrite !inE !imageP=> -[[a] [a_in_A <-]].
  move=> h; exists a; rewrite !inE a_in_A /= -negP=> a_in_B.
  by move: h=> /=; exists a.
qed.

(* -------------------------------------------------------------------- *)
lemma fcard_image_leq (f : 'a -> 'b) (A : 'a fset):
  card (image f A) <= card A.
proof.
  elim/fset_ind: A=> [|x A x_notin_A ih]; 1: by rewrite image0 !fcards0.
  rewrite imageU image1 (lez_trans (card (image f A) + 1)).
    by rewrite fcardU fcard1 ler_naddr 1:oppr_le0 1:fcard_ge0.
  rewrite fcardU fsetI1 x_notin_A fcards0 fcard1 oppz0 addz0.
  by rewrite ler_add2r.
qed.

lemma inj_fcard_image (f : 'a -> 'b) (A : 'a fset) :
    injective f => card (image f A) = card A.
proof.
move => inj_f.
have/oflist_uniq uniq_f : uniq (map f (elems A)).
  apply map_inj_in_uniq => *; [exact inj_f|exact uniq_elems].
by rewrite /image /card -(perm_eq_size _ _ uniq_f) size_map.
qed.

(* -------------------------------------------------------------------- *)
op [opaque] product (A : 'a fset) (B : 'b fset): ('a * 'b) fset =
  oflist (allpairs (fun x y => (x,y)) (elems A) (elems B)).
lemma productE (A : 'a fset) (B : 'b fset):
  product A B = oflist (allpairs (fun x y => (x,y)) (elems A) (elems B)).
proof. by rewrite/product. qed.

lemma productP (A : 'a fset) (B : 'b fset) (a : 'a) (b : 'b):
  (a, b) \in product A B <=> (a \in A) /\ (b \in B).
proof.
by rewrite productE mem_oflist allpairsP; split => [/#|*]; exists (a,b) => /#. 
qed.

lemma card_product (A B : 'a fset): 
  card (product A B) = card A * card B.
proof.
rewrite productE uniq_card_oflist ?size_allpairs -?cardE //.
apply allpairs_uniq; smt(uniq_elems).
qed.

(* -------------------------------------------------------------------- *)
op [opaque] fold (f : 'a -> 'b -> 'b) (z : 'b) (A : 'a fset) : 'b =
  foldr f z (elems A).
lemma foldE (f : 'a -> 'b -> 'b) z A: fold f z A = foldr f z (elems A).
proof. by rewrite/fold. qed.

lemma fold0 (f : 'a -> 'b -> 'b) (z : 'b): fold f z fset0 = z.
proof. by rewrite foldE elems_fset0. qed.

lemma fold1 (f : 'a -> 'b -> 'b) (z : 'b) (a : 'a):
  fold f z (fset1 a) = f a z.
proof. by rewrite foldE elems_fset1. qed.

lemma foldC (a : 'a) (f : 'a -> 'b -> 'b) (z : 'b) (A : 'a fset):
  (forall a a' b, f a (f a' b) = f a' (f a b)) =>
  mem A a =>
  fold f z A = f a (fold f z (A `\` fset1 a)).
proof.
  move=> f_commutative a_in_A; rewrite !foldE (foldr_rem a)// 1:-memE//.
  congr; apply/foldr_perm=> //.
  rewrite setDE rem_filter 1:uniq_elems//.
  have ->: predC (mem (fset1 a)) = predC1 a (* FIXME: views *)
    by apply/fun_ext=> x; rewrite /predC /predC1 in_fset1.
  rewrite -{1}(undup_id (filter (predC1 a) (elems A))) 2:oflistK//.
  by apply/filter_uniq/uniq_elems.
qed.

(* -------------------------------------------------------------------- *)

op rangeset (m n : int) = oflist (range m n).

lemma card_rangeset m n : card (rangeset m n) = max 0 (n - m).
proof. by rewrite uniq_card_oflist ?range_uniq size_range. qed.

lemma mem_rangeset m n i : i \in rangeset m n <=> m <= i && i < n.
proof. by rewrite mem_oflist mem_range. qed.

(* -------------------------------------------------------------------- *)
